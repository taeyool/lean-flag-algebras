import LeanFlagAlgebras.MetaTheory.SubstitutionBlowup
import LeanFlagAlgebras.MetaTheory.PlantedEstimate

/-! # Planted mass and planted estimate for the generalised blow-up (paper §6–§7)

This file lifts the two §5 quantitative estimates — `lem:planted-mass` and `lem:planted-estimate`
— from the independent blow-up to the generalised blow-up `subBlowup G W` (which covers the
complete blow-up `G^{m,+}` of §6 and the substitution `G[H_v]` of §7).

* `planted_mass_sub` (`lem:true-planted-estimate` / `lem:substitution-planting-estimate`, mass
  part): a uniformly random induced embedding of the type into `subBlowup G W` is planted with
  probability `≥ (λ/2k)^k`.  The planted labellings are induced embeddings for *any* within-class
  family `W` (distinct labels land in distinct clone classes, where adjacency is the base value),
  and the all-embeddings count is still `≤ N^k`, so the §5 argument carries over verbatim.

* `planted_estimate_sub` (`lem:true-planted-estimate` / `lem:substitution-planting-estimate`,
  approximation part): the density of `F₀` in the planted `subBlowup` differs from its density in
  the base by at most `1 − ρ`.  This is the host-generic `planted_estimate_host`, instantiated at
  `B = subBlowupLabeledGraph m W θ c`; the required good-event agreement is
  `good_event_induces_iff_sub`.
-/

open Finset Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras LabeledSubgraph SimpleGraph

variable {n k ℓ : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin k)}

/-! ## Planted mass for the generalised blow-up -/

/-- All *ordered* induced embeddings of the type graph `H` into the generalised blow-up
`subBlowup G W`. -/
noncomputable def blowupEmbeddings_sub (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin k))
    (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v))) :
    Finset (Fin k → Σ v : Fin n, Fin (m v)) :=
  univ.filter fun g =>
    Function.Injective g ∧ ∀ i j, H.Adj i j ↔ (subBlowup G W).Adj (g i) (g j)

/-- The §5 planted embeddings are induced embeddings of the generalised blow-up too: distinct
labels go to distinct clone classes, where the adjacency is the off-diagonal base value. -/
lemma plantedEmbeddings_subset_sub (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v))) (θ : H ↪g G) :
    plantedEmbeddings m θ ⊆ blowupEmbeddings_sub G H m W := by
  intro g hg
  rw [plantedEmbeddings, Finset.mem_image] at hg
  obtain ⟨c, -, rfl⟩ := hg
  rw [blowupEmbeddings_sub, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro a b hab
    exact θ.injective (congrArg Sigma.fst hab)
  · intro i j
    by_cases hij : i = j
    · subst hij; simp only [SimpleGraph.irrefl]
    · have hθ : (θ j) ≠ (θ i) := fun h => hij (θ.injective h.symm)
      rw [subBlowup_adj_of_fst_ne G W hθ]
      exact θ.map_adj_iff.symm

/-- The total number of induced embeddings into the generalised blow-up is at most `N^k`. -/
lemma blowupEmbeddings_sub_card_le (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin k))
    (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v))) :
    (blowupEmbeddings_sub G H m W).card ≤ (∑ v, m v) ^ k := by
  calc (blowupEmbeddings_sub G H m W).card
      ≤ (univ : Finset (Fin k → Σ v : Fin n, Fin (m v))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = (∑ v, m v) ^ k := by
        rw [Finset.card_univ, Fintype.card_pi]
        simp [Fintype.card_sigma]

/-- **Positive probability of the planted root, generalised** (`lem:true-planted-estimate` /
`lem:substitution-planting-estimate`, mass part).  When each labelled clone class is large enough
(`m(θ i) ≥ (λ/2k)·N`), a uniformly random induced embedding of the type into `subBlowup G W` is
planted with probability at least `(λ/2k)^k`.  The within-class family `W` is irrelevant: planted
embeddings and the `N^k` upper bound do not see it. -/
theorem planted_mass_sub (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v))) (θ : H ↪g G)
    {lam : ℚ} (hlam : 0 < lam) (hk : 0 < k) (hm : ∀ v, 1 ≤ m v)
    (hsize : ∀ i, lam / (2 * k) * ((∑ v, m v : ℕ) : ℚ) ≤ (m (θ i) : ℚ)) :
    (lam / (2 * k)) ^ k ≤
      ((plantedEmbeddings m θ).card : ℚ) / ((blowupEmbeddings_sub G H m W).card : ℚ) := by
  set N : ℕ := ∑ v, m v with hN
  set base : ℚ := lam / (2 * k) with hbase
  have hbase_nonneg : 0 ≤ base := by positivity
  have hPA : (plantedEmbeddings m θ).card ≤ (blowupEmbeddings_sub G H m W).card :=
    Finset.card_le_card (plantedEmbeddings_subset_sub m W θ)
  have hAN : (blowupEmbeddings_sub G H m W).card ≤ N ^ k := blowupEmbeddings_sub_card_le G H m W
  have hPpos : 0 < (plantedEmbeddings m θ).card := by
    rw [plantedEmbeddings_card]
    exact Finset.prod_pos fun i _ => lt_of_lt_of_le Nat.zero_lt_one (hm (θ i))
  have hApos : 0 < ((blowupEmbeddings_sub G H m W).card : ℚ) := by
    exact_mod_cast lt_of_lt_of_le hPpos hPA
  have hPlow : base ^ k * (N : ℚ) ^ k ≤ ((plantedEmbeddings m θ).card : ℚ) := by
    rw [plantedEmbeddings_card, Nat.cast_prod, ← mul_pow]
    calc (base * (N : ℚ)) ^ k = ∏ _i : Fin k, base * (N : ℚ) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i, ((m (θ i)) : ℚ) := by
          refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => hsize i)
          positivity
  rw [le_div_iff₀ hApos]
  calc base ^ k * ((blowupEmbeddings_sub G H m W).card : ℚ)
      ≤ base ^ k * (N : ℚ) ^ k := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hbase_nonneg k)
        exact_mod_cast hAN
    _ ≤ ((plantedEmbeddings m θ).card : ℚ) := hPlow

/-! ## Planted estimate for the generalised blow-up -/

/-- **Reduced planted estimate, generalised** (`lem:true-planted-estimate` /
`lem:substitution-planting-estimate`, approximation part).  The density of `F₀` in the planted
generalised blow-up differs from its density in the base by at most `1 − ρ`, with the same `ρ` as
in §5.  This is `planted_estimate_host` at `B = subBlowupLabeledGraph m W θ c`, whose good-event
agreement is `good_event_induces_iff_sub`. -/
theorem planted_estimate_sub (m : Fin n → ℕ) (W : ∀ v, SimpleGraph (Fin (m v))) (θ : H ↪g G)
    (c : ∀ i, Fin (m (θ i))) (F₀ : LabeledGraph H (Fin ℓ)) (M : ℕ)
    (hM : ∀ v, v ∉ Finset.image (fun t => θ t) Finset.univ → m v = M) :
    |flagDensity₁ (⟦F₀⟧ : Flag H (Fin ℓ))
        (⟦subBlowupLabeledGraph m W θ c⟧ : Flag H (Σ v : Fin n, Fin (m v)))
       - flagDensity₁ (⟦F₀⟧ : Flag H (Fin ℓ)) (⟦baseLabeledGraph θ⟧ : Flag H (Fin n))|
      ≤ 1 - (M ^ (ℓ - k) * ((n - k).choose (ℓ - k)) : ℚ)
            / (((∑ v, m v) - k).choose (ℓ - k)) := by
  refine planted_estimate_host m θ c F₀ M hM (subBlowupLabeledGraph m W θ c)
    (subBlowupLabeledGraph_type_verts m W θ c) ?_
  intro S' hinj hr hr'
  -- `good_event_induces_iff_sub` needs the base-roots projection bound.
  have hπ : (baseLabeledGraph θ).type_verts ⊆ Sigma.fst '' (↑S' : Set (Σ v : Fin n, Fin (m v))) := by
    rw [← blowupLabeledGraph_type_verts_image m θ c]
    exact Set.image_mono hr'
  -- Both sides equal "the base induces F₀ on the projection", via the two good-event lemmas.
  exact (good_event_induces_iff_sub (S' := (↑S' : Set (Σ v : Fin n, Fin (m v))))
      m W θ c hinj hr hπ F₀).trans
    (good_event_induces_iff (S' := (↑S' : Set (Σ v : Fin n, Fin (m v))))
      m θ c hinj hr' hπ F₀).symm

end FlagAlgebras.MetaTheory
