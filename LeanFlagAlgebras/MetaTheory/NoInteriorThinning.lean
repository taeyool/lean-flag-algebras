import LeanFlagAlgebras.MetaTheory.EdgeThinningLimit
import LeanFlagAlgebras.MetaTheory.CapstoneShared

/-! # No interior pinning, via the edge-thinned limit (paper §9.4, `thm:no-interior`)

This is the top of the §9.4 stack.  Using the edge-thinned constrained limits `φ₀^λ` of
[`EdgeThinningLimit`](./EdgeThinningLimit.lean), we produce a single **`{0,1}`-valued** positive
homomorphism `ψ_σ ∈ S_σ`, and conclude `thm:no-interior`: any `σ`-flag pinned to `c` on `S_σ` has
`c ∈ {0,1}`.

**The boolean point.**  Take `λ_k → 0` and the thinned limits `φ_k := φ₀^{λ_k} ∈ Q₀`, each with
positive `σ`-density, so each admits a random extension `ℙ[φ_k]`.  The flag-moment of a `σ`-flag `F`
under `ℙ[φ_k]` is
  `∫ χ(F) dℙ[φ_k] = φ_k⟦F⟧₀ / φ_k⟦1⟧₀ = (dnf_F · φ_k(⟨F⟩)) / (dnf_1 · φ_k⟨σ⟩₀)`.
The σ-density bound `φ_k⟨σ⟩₀ ≥ λ_k^{e(σ)}·φ₀⟨σ⟩₀` and the flag bound `φ_k(M) ≤ C·λ_k^{e(M)}` make this
ratio `O(λ_k^{e(⟨F⟩)−e(σ)})`, which `→ 0` whenever `F` has a new (non-root) edge, while the unique
edgeless extension of each size `→ 1` (the flags of a size sum to the unit).  Thus the moments
converge to the `{0,1}`-valued profile `b`; the measures `ℙ[φ_k]` converge weakly to the Dirac at the
positive homomorphism `ψ_σ` with `ψ_σ = b` (uniqueness of a measure by its flag-integrals), and a
Portmanteau/cylinder argument places `ψ_σ ∈ S_σ`.
-/

open MeasureTheory SimpleGraph Filter
open scoped Topology

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

attribute [local instance 0] Classical.propDecidable

/-! ## Edgeless ("cloud") `σ`-flags and the boolean profile

A `σ`-flag is *edgeless* when its underlying graph is exactly the image of `σ` under its type
embedding (so the non-root vertices are isolated and there are no root–non-root edges).  The
canonical edgeless `σ`-flag of size `s` is `default : FlagWithSize σ s`.  We show every `σ`-flag is
edgeless if and only if its underlying graph has exactly `e(σ)` edges, and that the densities of the
"cloud" sequence `σ ⊎ \bar K_m` converge to the `{0,1}`-valued profile `bProfile`. -/

/-- The standard inclusion `Fin n₀ ↪ Fin (n₀ + m)`. -/
private def cloudIncl (m : ℕ) : Fin n₀ ↪ Fin (n₀ + m) :=
  (Fin.castAddOrderEmb m).toEmbedding

/-- The edgeless extension `σ ⊎ \bar K_m`: `σ` on the first `n₀` vertices, the other `m` isolated. -/
private def cloudLabeled (m : ℕ) : LabeledGraph σ (Fin (n₀ + m)) :=
  { graph := σ.map (cloudIncl m), type_embed := SimpleGraph.Embedding.map (cloudIncl m) σ }

/-- The cloud flag sequence rooted at `σ`, with strictly increasing sizes `n₀ + m`. -/
private noncomputable def cloudSeq : FlagSeq σ := fun m => ⟨n₀ + m, ⟦cloudLabeled m⟧⟩

/-- The canonical edgeless `σ`-labelled graph of size `s` (`= default`). -/
private def canonLabeled (s : ℕ) (hs : n₀ ≤ s) : LabeledGraph σ (Fin s) :=
  (labeledGraph_inhabited σ (n := s) hs).default

/-- The canonical edgeless `σ`-flag of size `s`. -/
private noncomputable def canonFlag (s : ℕ) (hs : n₀ ≤ s) : Flag σ (Fin s) :=
  ⟦canonLabeled s hs⟧

/-- A `σ`-flag carrier is *edgeless* when its graph is the `σ`-image of its type embedding. -/
private def IsEdgeless {V : Type} (Fr : LabeledGraph σ V) : Prop :=
  Fr.graph = σ.map Fr.type_embed.toEmbedding

/-- The `σ`-image of the type embedding is a subgraph of the carrier graph. -/
private theorem map_type_embed_le {V : Type} (Fr : LabeledGraph σ V) :
    σ.map Fr.type_embed.toEmbedding ≤ Fr.graph := by
  intro x y h
  rw [SimpleGraph.map_adj] at h
  obtain ⟨a, b, hab, rfl, rfl⟩ := h
  simpa using Fr.type_embed.map_rel_iff.mpr hab

/-- Edge count of `σ.map f`, as an `Set.ncard` (avoids `Fintype`-instance mismatches). -/
private theorem ncard_map_edgeSet {V : Type} (f : Fin n₀ ↪ V) :
    (σ.map f).edgeSet.ncard = σ.edgeFinset.card := by
  rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ f.sym2Map.injective,
    ← Set.ncard_coe_finset σ.edgeFinset, SimpleGraph.coe_edgeFinset]

private theorem edgeFinset_card_eq_ncard {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    G.edgeFinset.card = G.edgeSet.ncard := by
  rw [← Set.ncard_coe_finset G.edgeFinset, SimpleGraph.coe_edgeFinset]

/-- An edgeless carrier has exactly `e(σ)` edges. -/
private theorem edgeless_card {V : Type} [Fintype V] [DecidableEq V] {Fr : LabeledGraph σ V}
    (h : IsEdgeless Fr) : Fr.graph.edgeFinset.card = σ.edgeFinset.card := by
  rw [edgeFinset_card_eq_ncard, h, ncard_map_edgeSet]

/-- Every `σ`-flag carrier has at least `e(σ)` edges. -/
private theorem edges_ge {V : Type} [Fintype V] [DecidableEq V] (Fr : LabeledGraph σ V) :
    σ.edgeFinset.card ≤ Fr.graph.edgeFinset.card := by
  rw [edgeFinset_card_eq_ncard Fr.graph, ← ncard_map_edgeSet Fr.type_embed.toEmbedding]
  refine Set.ncard_le_ncard ?_ Fr.graph.edgeSet.toFinite
  rw [SimpleGraph.edgeSet_subset_edgeSet]
  exact map_type_embed_le Fr

/-- A carrier with exactly `e(σ)` edges is edgeless. -/
private theorem edges_eq_imp_edgeless {V : Type} [Fintype V] [DecidableEq V] (Fr : LabeledGraph σ V)
    (h : Fr.graph.edgeFinset.card = σ.edgeFinset.card) : IsEdgeless Fr := by
  have hsub : (σ.map Fr.type_embed.toEmbedding).edgeSet ⊆ Fr.graph.edgeSet := by
    rw [SimpleGraph.edgeSet_subset_edgeSet]; exact map_type_embed_le Fr
  have hncard : Fr.graph.edgeSet.ncard ≤ (σ.map Fr.type_embed.toEmbedding).edgeSet.ncard := by
    rw [ncard_map_edgeSet, ← edgeFinset_card_eq_ncard]; exact le_of_eq h
  have heqset := Set.eq_of_subset_of_ncard_le hsub hncard Fr.graph.edgeSet.toFinite
  exact (SimpleGraph.edgeSet_injective heqset).symm

/-- **Reindexing edgeless flags.**  Any two edgeless `σ`-flags on equinumerous vertex sets are
isomorphic (their underlying graphs are both `σ` mapped via an injection, matched up vertex-wise). -/
private theorem reindex_edgeless {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {Fr : LabeledGraph σ V} {Gr : LabeledGraph σ W} (hcard : Fintype.card V = Fintype.card W)
    (hF : IsEdgeless Fr) (hG : IsEdgeless Gr) : Nonempty (Fr ≃f Gr) := by
  classical
  set te : Fin n₀ ↪ V := Fr.type_embed.toEmbedding with hte
  set te' : Fin n₀ ↪ W := Gr.type_embed.toEmbedding with hte'
  have hcr : Fintype.card ↥(Set.range ⇑te) = n₀ := by
    rw [Fintype.card_congr (Equiv.ofInjective ⇑te te.injective).symm, Fintype.card_fin]
  have hcr' : Fintype.card ↥(Set.range ⇑te') = n₀ := by
    rw [Fintype.card_congr (Equiv.ofInjective ⇑te' te'.injective).symm, Fintype.card_fin]
  have hcompl : Fintype.card ↥(Set.range ⇑te)ᶜ = Fintype.card ↥(Set.range ⇑te')ᶜ := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, hcr, hcr', hcard]
  let e₀ : ↥(Set.range ⇑te) ≃ ↥(Set.range ⇑te') :=
    (Equiv.ofInjective ⇑te te.injective).symm.trans (Equiv.ofInjective ⇑te' te'.injective)
  have he₀ : ∀ i : Fin n₀, (e₀ ⟨te i, ⟨i, rfl⟩⟩ : W) = te' i := by
    intro i
    have hi : (Equiv.ofInjective ⇑te te.injective).symm ⟨te i, ⟨i, rfl⟩⟩ = i := by
      rw [Equiv.symm_apply_eq, Equiv.ofInjective_apply]
    show ((Equiv.ofInjective ⇑te' te'.injective)
      ((Equiv.ofInjective ⇑te te.injective).symm ⟨te i, ⟨i, rfl⟩⟩) : W) = te' i
    rw [hi, Equiv.ofInjective_apply]
  let e₁ : ↥(Set.range ⇑te)ᶜ ≃ ↥(Set.range ⇑te')ᶜ := Fintype.equivOfCardEq hcompl
  let ee := ((Equiv.Set.compl e₀).symm) e₁
  let e : V ≃ W := ee.1
  have heq : ∀ i : Fin n₀, e (te i) = te' i := by
    intro i
    have h2 : e (te i) = ↑(e₀ ⟨te i, ⟨i, rfl⟩⟩) := ee.2 ⟨te i, ⟨i, rfl⟩⟩
    rw [h2, he₀ i]
  refine ⟨{ graph_iso := ⟨e, ?_⟩, type_preserve := ?_ }⟩
  · intro a b
    show Gr.graph.Adj (e a) (e b) ↔ Fr.graph.Adj a b
    rw [hF, hG, SimpleGraph.map_adj, SimpleGraph.map_adj]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨u, v, huv, e.injective ?_, e.injective ?_⟩
      · rw [heq u]; exact hu
      · rw [heq v]; exact hv
    · rintro ⟨u, v, huv, rfl, rfl⟩
      exact ⟨u, v, huv, (heq u).symm, (heq v).symm⟩
  · funext i
    show e (Fr.type_embed i) = Gr.type_embed i
    exact heq i

/-- **Edgeless ⇔ `e(σ)` edges ⇔ canonical.**  For a `σ`-flag `F`, its underlying graph equals
`canonFlag` (the edgeless flag) exactly when it has `e(σ)` edges. -/
private theorem canon_iff_edges (F : FinFlag σ) :
    F.2 = canonFlag F.1 (finFlag_size_ge_n₀ F)
      ↔ F.2.out.graph.edgeFinset.card = σ.edgeFinset.card := by
  set hns := finFlag_size_ge_n₀ F with hhns
  have hcanon_edgeless : IsEdgeless (σ := σ) (canonLabeled (σ := σ) F.1 hns) := by rfl
  constructor
  · intro hc
    have hcq : (⟦F.2.out⟧ : Flag σ (Fin F.1)) = (⟦canonLabeled F.1 hns⟧ : Flag σ (Fin F.1)) := by
      rw [Quotient.out_eq]; exact hc
    obtain ⟨φ⟩ := Quotient.exact hcq
    rw [φ.graph_iso.card_edgeFinset_eq]
    exact edgeless_card hcanon_edgeless
  · intro hedge
    have hFedgeless : IsEdgeless F.2.out := edges_eq_imp_edgeless F.2.out hedge
    obtain ⟨φ⟩ := reindex_edgeless (Fr := F.2.out) (Gr := canonLabeled (σ := σ) F.1 hns)
      (by simp) hFedgeless hcanon_edgeless
    show F.2 = ⟦canonLabeled F.1 hns⟧
    rw [← Quotient.out_eq F.2]
    exact Quotient.sound ⟨φ⟩

/-- A graph embedding does not increase the edge count. -/
private theorem embedding_edges_le {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} (g : G ↪g H) :
    G.edgeFinset.card ≤ H.edgeFinset.card := by
  rw [edgeFinset_card_eq_ncard G, edgeFinset_card_eq_ncard H,
    ← Set.ncard_image_of_injective G.edgeSet g.toEmbedding.sym2Map.injective]
  refine Set.ncard_le_ncard ?_ H.edgeSet.toFinite
  rintro _ ⟨e', he', rfl⟩
  induction e' with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at he'
    show Sym2.map g.toEmbedding s(a, b) ∈ H.edgeSet
    rw [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet]
    exact g.map_rel_iff.mpr he'

/-- **The cloud density is the canonical indicator.**  For `|F| ≤ n₀ + m`, the density of `F` in the
cloud `σ ⊎ \bar K_m` is `1` if `F` is the canonical edgeless flag and `0` otherwise. -/
private theorem cloud_density_eq (F : FinFlag σ) (m : ℕ) (hsm : F.1 ≤ n₀ + m) :
    flagDensity₁ F.2 (⟦cloudLabeled m⟧ : Flag σ (Fin (n₀ + m)))
      = if F.2 = canonFlag F.1 (finFlag_size_ge_n₀ F) then 1 else 0 := by
  set s := F.1 with hs
  have hns : n₀ ≤ s := finFlag_size_ge_n₀ F
  have key1 : ∀ F' : Flag σ (Fin s),
      flagDensity₁ F' (⟦cloudLabeled m⟧ : Flag σ (Fin (n₀ + m))) ≠ 0 → F' = canonFlag s hns := by
    intro F' hF'
    rw [← Quotient.out_eq F'] at hF'
    obtain ⟨S, hroot, ⟨φiso⟩⟩ :=
      exists_inducing_subset_of_flagDensity₁_ne_zero F'.out (cloudLabeled m) hF'
    -- `F'.out.graph` embeds (induced) into the cloud, so has at most `e(σ)` edges; at least `e(σ)`.
    have hcoeEmb : (LabeledSubgraph.inducedLabeledSubgraph (cloudLabeled m)
        (↑S : Set (Fin (n₀ + m))) hroot).coe.graph ↪g (cloudLabeled m).graph :=
      { toFun := fun u => u.val
        inj' := fun u v h => Subtype.ext h
        map_rel_iff' := by
          intro u v
          rw [LabeledSubgraph.coe_adj_iff]
          exact ⟨fun h => ⟨u.2, v.2, h⟩, fun h => h.2.2⟩ }
    have hemb : F'.out.graph ↪g (cloudLabeled m).graph :=
      hcoeEmb.comp φiso.graph_iso.symm.toEmbedding
    have hcloud : (cloudLabeled m).graph.edgeFinset.card = σ.edgeFinset.card :=
      edgeless_card (Fr := cloudLabeled m) rfl
    have hle : F'.out.graph.edgeFinset.card ≤ σ.edgeFinset.card := by
      rw [← hcloud]; exact embedding_edges_le hemb
    have hedge : F'.out.graph.edgeFinset.card = σ.edgeFinset.card :=
      le_antisymm hle (edges_ge F'.out)
    have := (canon_iff_edges ⟨s, F'⟩).mpr hedge
    simpa using this
  have hsum : (∑ F' : Flag σ (Fin s),
      flagDensity₁ F' (⟦cloudLabeled m⟧ : Flag σ (Fin (n₀ + m)))) = 1 := by
    have hchain := flagDensity_eq_sum_density_prods (σ := σ) s (emptyFlag σ)
      (⟦cloudLabeled m⟧ : Flag σ (Fin (n₀ + m))) (le_refl n₀) hns hsm
    rw [flagDensity_empty] at hchain
    rw [hchain]
    apply Finset.sum_congr rfl
    intro F' _
    rw [flagDensity_empty, one_mul]
  by_cases hc : F.2 = canonFlag s hns
  · rw [if_pos hc, hc]
    have hcanon : flagDensity₁ (canonFlag s hns)
        (⟦cloudLabeled m⟧ : Flag σ (Fin (n₀ + m)))
        = ∑ F' : Flag σ (Fin s), flagDensity₁ F' (⟦cloudLabeled m⟧ : Flag σ (Fin (n₀ + m))) := by
      symm
      apply Finset.sum_eq_single_of_mem (canonFlag s hns) (Finset.mem_univ _)
      intro F' _ hne
      by_contra h0
      exact hne (key1 F' h0)
    rw [hcanon, hsum]
  · rw [if_neg hc]
    by_contra h0
    exact hc (key1 F.2 h0)

/-- The `{0,1}`-valued boolean profile: `1` on the canonical edgeless flag of each size, else `0`. -/
private noncomputable def bProfile (F : FinFlag σ) : ℝ :=
  if F.2 = canonFlag F.1 (finFlag_size_ge_n₀ F) then 1 else 0

private theorem bProfile_mem_Icc (F : FinFlag σ) : bProfile F ∈ Set.Icc (0 : ℝ) 1 := by
  unfold bProfile; split <;> simp

/-- The boolean profile as a point of `FlagDensitySpace σ`. -/
private noncomputable def bvec : FlagDensitySpace σ :=
  ⟨bProfile, by
    simp only [FlagDensitySpace, Set.pi_univ_Icc, Set.mem_Icc]
    exact ⟨fun F => (bProfile_mem_Icc F).1, fun F => (bProfile_mem_Icc F).2⟩⟩

private theorem cloud_converges : ConvergesTo cloudSeq (bvec : FlagDensitySpace σ) := by
  rw [flagSeq_convergesTo_iff]
  refine ⟨?_, ?_⟩
  · intro a b hab
    show n₀ + a < n₀ + b
    omega
  · intro F
    have heq : ∀ m, F.1 ≤ n₀ + m → flagDensitySeq cloudSeq m F = bProfile F := by
      intro m hm
      show (flagDensity₁ F.2 (cloudSeq m).2 : ℝ) = bProfile F
      have : (cloudSeq m).2 = (⟦cloudLabeled m⟧ : Flag σ (Fin (n₀ + m))) := rfl
      rw [this, cloud_density_eq F m hm]
      unfold bProfile
      split <;> simp
    have hee : (fun _ => bProfile F) =ᶠ[atTop] (fun m => flagDensitySeq cloudSeq m F) := by
      filter_upwards [eventually_ge_atTop F.1] with m hm
      exact (heq m (by omega)).symm
    have hbF : (bvec : FlagDensitySpace σ) F = bProfile F := rfl
    rw [hbF]
    exact tendsto_const_nhds.congr' hee

/-- There is a positive homomorphism point of `FlagDensitySpace σ` realising the
`{0,1}`-valued boolean profile `bProfile`. -/
private theorem exists_bool_psi :
    ∃ ψ : PositiveHomSpace σ, ∀ F : FinFlag σ, ψ.val F = bProfile F := by
  obtain ⟨φ, hφ⟩ := flagSeq_limit_mem_positiveHom cloudSeq cloud_converges
  exact ⟨⟨bvec, ⟨φ, hφ⟩⟩, fun F => rfl⟩

/-- The unlabelled underlying graph has the same edge count as the labelled one. -/
private theorem unlabel_edges (G : FinFlag σ) :
    (unlabel G.2).out.graph.edgeFinset.card = G.2.out.graph.edgeFinset.card := by
  have h : (⟦(unlabel G.2).out⟧ : Flag ∅ₜ (Fin G.1))
      = (⟦unlabeledGraph G.2.out⟧ : Flag ∅ₜ (Fin G.1)) := by
    rw [Quotient.out_eq]
    show unlabel G.2 = ⟦unlabeledGraph G.2.out⟧
    conv_lhs => rw [← Quotient.out_eq G.2]
    rfl
  obtain ⟨φ⟩ := Quotient.exact h
  exact φ.graph_iso.card_edgeFinset_eq

/-- **The boolean point of `S_σ`** (analytic heart of `thm:no-interior`).  For an edge-deletion-closed
hereditary class and a non-degenerate type `σ`, the root-planting set `S_σ` contains a positive
homomorphism that is `{0,1}`-valued on every flag — the `λ → 0` limit of the random extensions of the
edge-thinned constrained limits `φ₀^λ`. -/
theorem exists_boolean_point_in_Sσ (hc : HeredClass) (hedc : EdgeDeletionClosed hc)
    (hnd : ∃ φ₀ : PositiveHom ∅ₜ,
      posHomPoint φ₀ ∈ Qσ (hc.constraintOf σ).forb0 ∧ φ₀ ⟨σ⟩₀ > 0) :
    ∃ ψ ∈ Sσ (hc.constraintOf σ), ∀ F : FinFlag σ,
      (PositiveHomSpace.toPosHom ψ) ⟦basisVector F⟧ = 0 ∨
        (PositiveHomSpace.toPosHom ψ) ⟦basisVector F⟧ = 1 := by
  classical
  obtain ⟨φ₀, hφ₀Q, hφ₀σ⟩ := hnd
  obtain ⟨ψ, hψval⟩ := exists_bool_psi (σ := σ)
  set eσ := σ.edgeFinset.card with heσ
  -- The edge-thinned limits `φ_k` at `λ_k = 1/(k+2)`.
  set lam : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2) with hlam
  have hlam_pos : ∀ k, 0 < lam k := fun k => by rw [hlam]; positivity
  have hlam_le : ∀ k, lam k ≤ 1 := fun k => by
    rw [hlam, div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hlam_tendsto : Tendsto lam atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hlam, one_div] using h1.inv_tendsto_atTop
  have hex : ∀ k : ℕ, ∃ φlam : PositiveHom ∅ₜ,
      posHomPoint φlam ∈ Qσ (hc.constraintOf σ).forb0 ∧
      lam k ^ eσ * φ₀ ⟨σ⟩₀ ≤ φlam ⟨σ⟩₀ ∧
      ∀ M : FinFlag ∅ₜ, φlam.coe M
        ≤ ((M.1.choose 2).choose (M.2.out.graph.edgeFinset.card) : ℝ)
            * lam k ^ (M.2.out.graph.edgeFinset.card) :=
    fun k => exists_thinned_limit hc hedc σ φ₀ hφ₀Q (lam k) (hlam_pos k) (hlam_le k)
  choose φk hφkQ hφkσ hφkM using hex
  have hσk : ∀ k, (φk k) ⟨σ⟩₀ > 0 := fun k =>
    lt_of_lt_of_le (mul_pos (pow_pos (hlam_pos k) eσ) hφ₀σ) (hφkσ k)
  set P : ℕ → MeasureTheory.Measure (PositiveHomSpace σ) :=
    fun k => (probMeasure_extend_emptyType_positiveHom (φk k) (hσk k) : MeasureTheory.Measure _)
    with hP
  have hPprob : ∀ k, IsProbabilityMeasure (P k) := fun k => by rw [hP]; infer_instance
  -- abbreviation for the flag-moment.
  set mom : ℕ → FinFlag σ → ℝ :=
    fun k G => ∫ χ, (PositiveHomSpace.toPosHom χ) ⟦basisVector G⟧ ∂(P k) with hmom
  have hdnf1_pos : (0 : ℝ) < (downwardNormalizingFactor (emptyFlag σ) : ℝ) := by
    simp only [Rat.cast_pos]; exact downwardNormalizingFactor_emptyFlag_pos
  -- The flag-moment formula.
  have hmoment : ∀ k (G : FinFlag σ), mom k G
      = ((downwardNormalizingFactor G.2 : ℝ) * (φk k).coe ⟨G.1, unlabel G.2⟩)
          / ((downwardNormalizingFactor (emptyFlag σ) : ℝ) * (φk k) ⟨σ⟩₀) := by
    intro k G
    have hspec := probMeasure_extend_emptyType_positiveHom_spec (hσk k) (⟦basisVector G⟧ : FlagAlgebra σ)
    have hnum : (φk k) (downward (⟦basisVector G⟧ : FlagAlgebra σ))
        = (downwardNormalizingFactor G.2 : ℝ) * (φk k).coe ⟨G.1, unlabel G.2⟩ := by
      rw [downward_basisVector G, PositiveHom.map_smul, PositiveHom.coe_flag]
    have hden : (φk k) (downward (1 : FlagAlgebra σ))
        = (downwardNormalizingFactor (emptyFlag σ) : ℝ) * (φk k) ⟨σ⟩₀ := by
      rw [one_downward_eq, PositiveHom.map_smul]
    show (∫ χ, (PositiveHomSpace.toPosHom χ) ⟦basisVector G⟧ ∂(P k)) = _
    rw [show (P k) = (probMeasure_extend_emptyType_positiveHom (φk k) (hσk k)
      : MeasureTheory.Measure _) from rfl, hspec, hnum, hden]
  -- nonnegativity of the moment.
  have hmom_nonneg : ∀ k (G : FinFlag σ), 0 ≤ mom k G := by
    intro k G
    show 0 ≤ ∫ χ, (PositiveHomSpace.toPosHom χ) ⟦basisVector G⟧ ∂(P k)
    refine integral_nonneg (fun χ => ?_)
    exact positiveHom_basisVector_ge_zero (PositiveHomSpace.toPosHom χ) G
  -- Moments of new-edge flags vanish.
  have hmoment_zero : ∀ (G : FinFlag σ), eσ < G.2.out.graph.edgeFinset.card →
      Tendsto (fun k => mom k G) atTop (𝓝 0) := by
    intro G hG
    set eG := G.2.out.graph.edgeFinset.card with heG
    have heM : (unlabel G.2).out.graph.edgeFinset.card = eG := unlabel_edges G
    set C : ℝ := (downwardNormalizingFactor G.2 : ℝ) * ((G.1.choose 2).choose eG : ℝ)
        / ((downwardNormalizingFactor (emptyFlag σ) : ℝ) * φ₀ ⟨σ⟩₀) with hC
    have hbound : ∀ k, mom k G ≤ C * lam k ^ (eG - eσ) := by
      intro k
      rw [hmoment k G]
      have hcoe : (φk k).coe ⟨G.1, unlabel G.2⟩ ≤ ((G.1.choose 2).choose eG : ℝ) * lam k ^ eG := by
        have hb := hφkM k ⟨G.1, unlabel G.2⟩
        rw [heM] at hb
        exact hb
      have hsden : lam k ^ eσ * φ₀ ⟨σ⟩₀ ≤ (φk k) ⟨σ⟩₀ := hφkσ k
      have hposden : (0 : ℝ) < (downwardNormalizingFactor (emptyFlag σ) : ℝ) * (φk k) ⟨σ⟩₀ :=
        mul_pos hdnf1_pos (hσk k)
      have hdnfF : (0 : ℝ) ≤ (downwardNormalizingFactor G.2 : ℝ) := by
        exact_mod_cast downwardNormalizingFactor_nonneg G.2
      have hlamE : lam k ^ eG = lam k ^ eσ * lam k ^ (eG - eσ) := by
        rw [← pow_add]; congr 1; omega
      have hnum_le : (downwardNormalizingFactor G.2 : ℝ) * (φk k).coe ⟨G.1, unlabel G.2⟩
          ≤ (downwardNormalizingFactor G.2 : ℝ) * (((G.1.choose 2).choose eG : ℝ) * lam k ^ eG) :=
        mul_le_mul_of_nonneg_left hcoe hdnfF
      have hden_ge : (downwardNormalizingFactor (emptyFlag σ) : ℝ) * (lam k ^ eσ * φ₀ ⟨σ⟩₀)
          ≤ (downwardNormalizingFactor (emptyFlag σ) : ℝ) * (φk k) ⟨σ⟩₀ :=
        mul_le_mul_of_nonneg_left hsden hdnf1_pos.le
      have hposden2 : (0 : ℝ) < (downwardNormalizingFactor (emptyFlag σ) : ℝ) * (lam k ^ eσ * φ₀ ⟨σ⟩₀) :=
        mul_pos hdnf1_pos (mul_pos (pow_pos (hlam_pos k) eσ) hφ₀σ)
      have hlamσ_ne : lam k ^ eσ ≠ 0 := by positivity
      have hφ₀σ_ne : φ₀ ⟨σ⟩₀ ≠ 0 := ne_of_gt hφ₀σ
      have hdnf1_ne : (downwardNormalizingFactor (emptyFlag σ) : ℝ) ≠ 0 := ne_of_gt hdnf1_pos
      have hRHS : C * lam k ^ (eG - eσ)
          = (downwardNormalizingFactor G.2 : ℝ) * (((G.1.choose 2).choose eG : ℝ) * lam k ^ eG)
            / ((downwardNormalizingFactor (emptyFlag σ) : ℝ) * (lam k ^ eσ * φ₀ ⟨σ⟩₀)) := by
        rw [hC, hlamE]; field_simp
      have hcross : ((downwardNormalizingFactor G.2 : ℝ) * (φk k).coe ⟨G.1, unlabel G.2⟩)
            * ((downwardNormalizingFactor (emptyFlag σ) : ℝ) * (lam k ^ eσ * φ₀ ⟨σ⟩₀))
          ≤ ((downwardNormalizingFactor G.2 : ℝ) * (((G.1.choose 2).choose eG : ℝ) * lam k ^ eG))
            * ((downwardNormalizingFactor (emptyFlag σ) : ℝ) * (φk k) ⟨σ⟩₀) :=
        mul_le_mul hnum_le hden_ge hposden2.le (mul_nonneg hdnfF (by positivity))
      rw [hRHS, div_le_div_iff₀ hposden hposden2]
      exact hcross
    have htend : Tendsto (fun k => C * lam k ^ (eG - eσ)) atTop (𝓝 0) := by
      have hp : Tendsto (fun k => lam k ^ (eG - eσ)) atTop (𝓝 0) := by
        have := hlam_tendsto.pow (eG - eσ)
        rwa [zero_pow (by omega)] at this
      simpa using hp.const_mul C
    exact squeeze_zero (hmom_nonneg · G) hbound htend
  -- integrability of flag-evaluations under each `P k`.
  have hintegrable : ∀ k (f : FlagAlgebra σ),
      MeasureTheory.Integrable (fun χ : PositiveHomSpace σ => (PositiveHomSpace.toPosHom χ) f) (P k) := by
    intro k f
    haveI := hPprob k
    exact BoundedContinuousFunction.integrable _
      (BoundedContinuousFunction.mkOfCompact (evalContinuousMap f))
  -- The size-`s` moments sum to one.
  have hsum_moment : ∀ k (s : ℕ), n₀ ≤ s →
      (∑ F' : FlagWithSize σ s, mom k ⟨s, F'⟩) = 1 := by
    intro k s hs
    haveI := hPprob k
    have hpt : ∀ χ : PositiveHomSpace σ,
        (∑ F' : FlagWithSize σ s, (PositiveHomSpace.toPosHom χ) ⟦basisVector ⟨s, F'⟩⟧) = 1 := by
      intro χ
      rw [← PositiveHom.map_sum, sum_flagWithSize_eq_one s hs, PositiveHom.map_one]
    simp only [hmom]
    rw [← MeasureTheory.integral_finset_sum Finset.univ (fun F' _ => hintegrable k _),
      show (fun χ : PositiveHomSpace σ => ∑ F' : FlagWithSize σ s,
          (PositiveHomSpace.toPosHom χ) ⟦basisVector ⟨s, F'⟩⟧) = fun _ => (1 : ℝ) from funext hpt,
      MeasureTheory.integral_const, MeasureTheory.probReal_univ, smul_eq_mul, mul_one]
  -- The moment converges to the boolean profile.
  have hmoment_tendsto : ∀ (G : FinFlag σ), Tendsto (fun k => mom k G) atTop (𝓝 (bProfile G)) := by
    intro G
    by_cases hcanon : G.2 = canonFlag G.1 (finFlag_size_ge_n₀ G)
    · -- `bProfile G = 1`: isolate `G` in the size-`s` sum.
      have hbG : bProfile G = 1 := by rw [bProfile]; rw [if_pos hcanon]
      rw [hbG]
      set s := G.1 with hs
      have hns : n₀ ≤ s := finFlag_size_ge_n₀ G
      have hsplit : ∀ k, mom k G = 1 - ∑ F' ∈ Finset.univ.erase G.2, mom k ⟨s, F'⟩ := by
        intro k
        have hsum := hsum_moment k s hns
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ G.2)] at hsum
        have : mom k G = mom k ⟨s, G.2⟩ := rfl
        rw [this]; linarith
      have herase : Tendsto (fun k => ∑ F' ∈ Finset.univ.erase G.2, mom k ⟨s, F'⟩)
          atTop (𝓝 0) := by
        have : Tendsto (fun k => ∑ F' ∈ Finset.univ.erase G.2, mom k ⟨s, F'⟩)
            atTop (𝓝 (∑ F' ∈ Finset.univ.erase G.2, (0 : ℝ))) := by
          refine tendsto_finset_sum _ (fun F' hF' => ?_)
          rw [Finset.mem_erase] at hF'
          apply hmoment_zero ⟨s, F'⟩
          -- `F' ≠ G.2` so `⟨s,F'⟩` is not the canonical flag, hence has `> eσ` edges.
          have hne : (⟨s, F'⟩ : FinFlag σ).2 ≠ canonFlag (⟨s, F'⟩ : FinFlag σ).1 (finFlag_size_ge_n₀ _) := by
            intro hF'eq
            apply hF'.1
            have : F' = canonFlag s hns := by simpa using hF'eq
            rw [this, ← hcanon]
          have hedge_ne : (⟨s, F'⟩ : FinFlag σ).2.out.graph.edgeFinset.card ≠ eσ := by
            intro he; exact hne ((canon_iff_edges ⟨s, F'⟩).mpr he)
          exact lt_of_le_of_ne (edges_ge _) (Ne.symm hedge_ne)
        simpa using this
      have := herase.const_sub 1
      simp only [sub_zero] at this
      exact (this.congr (fun k => (hsplit k).symm))
    · -- `bProfile G = 0`: `G` has `> eσ` edges.
      have hbG : bProfile G = 0 := by rw [bProfile]; rw [if_neg hcanon]
      rw [hbG]
      have hedge_ne : G.2.out.graph.edgeFinset.card ≠ eσ := by
        intro he; exact hcanon ((canon_iff_edges G).mpr he)
      exact hmoment_zero G (lt_of_le_of_ne (edges_ge _) (Ne.symm hedge_ne))
  -- The absolute-deviation integral vanishes.
  have habs_tendsto : ∀ (Fi : FinFlag σ),
      Tendsto (fun k => ∫ χ, |χ.val Fi - bProfile Fi| ∂(P k)) atTop (𝓝 0) := by
    intro Fi
    haveI _hpp := hPprob
    have hcoordeq : (fun χ : PositiveHomSpace σ => χ.val Fi)
        = (fun χ => (PositiveHomSpace.toPosHom χ) ⟦basisVector Fi⟧) :=
      funext (fun χ => (PositiveHomSpace.toPosHom_basisVector χ Fi).symm)
    have hcoord : ∀ k, (∫ χ : PositiveHomSpace σ, (χ.val Fi) ∂(P k)) = mom k Fi := by
      intro k
      show (∫ χ : PositiveHomSpace σ, (χ.val Fi) ∂(P k))
        = ∫ χ, (PositiveHomSpace.toPosHom χ) ⟦basisVector Fi⟧ ∂(P k)
      rw [hcoordeq]
    have hintFi : ∀ k, MeasureTheory.Integrable (fun χ : PositiveHomSpace σ => χ.val Fi) (P k) := by
      intro k; rw [hcoordeq]; exact hintegrable k _
    by_cases hb : bProfile Fi = 0
    · have heqzero : ∀ k, (∫ χ, |χ.val Fi - bProfile Fi| ∂(P k)) = mom k Fi := by
        intro k
        rw [hb, ← hcoord k]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with χ
        rw [sub_zero, abs_of_nonneg]
        simpa [PositiveHomSpace.toPosHom_basisVector] using
          positiveHom_basisVector_ge_zero (PositiveHomSpace.toPosHom χ) Fi
      rw [tendsto_congr heqzero]
      have hmt := hmoment_tendsto Fi
      rwa [hb] at hmt
    · have hb1 : bProfile Fi = 1 := by
        rw [bProfile] at hb ⊢
        by_cases hc2 : Fi.2 = canonFlag Fi.1 (finFlag_size_ge_n₀ Fi)
        · rw [if_pos hc2]
        · rw [if_neg hc2] at hb; exact absurd rfl hb
      have heqone : ∀ k, (∫ χ, |χ.val Fi - bProfile Fi| ∂(P k)) = 1 - mom k Fi := by
        intro k
        haveI := hPprob k
        rw [hb1]
        have heq2 : (∫ χ : PositiveHomSpace σ, |χ.val Fi - 1| ∂(P k))
            = ∫ χ : PositiveHomSpace σ, ((1 : ℝ) - χ.val Fi) ∂(P k) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with χ
          rw [abs_of_nonpos (by
            have := positiveHom_basisVector_le_one (PositiveHomSpace.toPosHom χ) Fi
            rw [PositiveHomSpace.toPosHom_basisVector] at this; linarith)]
          ring
        rw [heq2, MeasureTheory.integral_sub (MeasureTheory.integrable_const 1) (hintFi k),
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, smul_eq_mul, mul_one,
          hcoord k]
      rw [tendsto_congr heqone]
      have hmt := (hmoment_tendsto Fi).const_sub 1
      rw [hb1] at hmt
      simpa using hmt
  -- assemble: `ψ ∈ S_σ` via the cylinder criterion, and `ψ` is `{0,1}`-valued.
  refine ⟨ψ, ?_, ?_⟩
  · apply mem_closure_of_forall_finset_cylinder
    intro Fs ε hε
    set g : PositiveHomSpace σ → ℝ := fun χ => ∑ Fi ∈ Fs, |χ.val Fi - bProfile Fi| with hg
    have hgcont : Continuous g := by
      apply continuous_finset_sum
      intro Fi _
      exact (continuous_posHomSpace_coord Fi).sub continuous_const |>.abs
    have hgnn : ∀ χ, 0 ≤ g χ := fun χ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hg_tendsto : Tendsto (fun k => ∫ χ, g χ ∂(P k)) atTop (𝓝 0) := by
      have hsum_eq : ∀ k, (∫ χ, g χ ∂(P k))
          = ∑ Fi ∈ Fs, ∫ χ, |χ.val Fi - bProfile Fi| ∂(P k) := by
        intro k
        haveI := hPprob k
        rw [hg]
        rw [MeasureTheory.integral_finset_sum]
        intro Fi _
        exact ((continuous_posHomSpace_coord Fi).sub continuous_const).abs.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      rw [tendsto_congr hsum_eq]
      have : Tendsto (fun k => ∑ Fi ∈ Fs, ∫ χ, |χ.val Fi - bProfile Fi| ∂(P k))
          atTop (𝓝 (∑ Fi ∈ Fs, (0 : ℝ))) :=
        tendsto_finset_sum _ (fun Fi _ => habs_tendsto Fi)
      simpa using this
    -- pick `k` with `∫ g dP_k < ε`.
    obtain ⟨k, hk⟩ : ∃ k, (∫ χ, g χ ∂(P k)) < ε := by
      have := (hg_tendsto.eventually (eventually_lt_nhds hε)).exists
      obtain ⟨k, hk⟩ := this
      exact ⟨k, by simpa using hk⟩
    haveI := hPprob k
    have hgint : MeasureTheory.Integrable g (P k) :=
      hgcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    -- Markov: the bad set `{g ≥ ε}` has measure `< 1`.
    have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
      (ae_of_all (P k) hgnn) hgint ε
    have hbadreal : (P k).real {χ | ε ≤ g χ} < 1 := by
      have hle : (P k).real {χ | ε ≤ g χ} ≤ (∫ χ, g χ ∂(P k)) / ε := by
        rw [le_div_iff₀ hε]; linarith [hmarkov]
      calc (P k).real {χ | ε ≤ g χ} ≤ (∫ χ, g χ ∂(P k)) / ε := hle
        _ < 1 := by rw [div_lt_one hε]; exact hk
    -- so the good set `{g < ε}` has positive real measure.
    have hmeas_bad : MeasurableSet {χ : PositiveHomSpace σ | ε ≤ g χ} :=
      measurableSet_le measurable_const hgcont.measurable
    have hgood_real : 0 < (P k).real {χ : PositiveHomSpace σ | g χ < ε} := by
      have hcompl : {χ : PositiveHomSpace σ | g χ < ε} = {χ | ε ≤ g χ}ᶜ := by
        ext χ; simp [not_le]
      rw [hcompl, MeasureTheory.measureReal_compl hmeas_bad, MeasureTheory.probReal_univ]
      linarith [hbadreal]
    -- positive-measure set meets the support.
    obtain ⟨χ, hχsupp, hχgood⟩ :
        ∃ χ, χ ∈ (P k).support ∧ g χ < ε := by
      by_contra hcon
      push_neg at hcon
      have hsub : {χ : PositiveHomSpace σ | g χ < ε} ⊆ (P k).supportᶜ := by
        intro χ hχ hχs
        exact absurd (hcon χ hχs) (not_le.mpr hχ)
      have hzero : (P k) {χ : PositiveHomSpace σ | g χ < ε} = 0 :=
        measure_mono_null hsub (MeasureTheory.Measure.measure_compl_support)
      have : (P k).real {χ : PositiveHomSpace σ | g χ < ε} = 0 := by
        rw [MeasureTheory.measureReal_def, hzero, ENNReal.toReal_zero]
      linarith [hgood_real]
    refine ⟨χ, ?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨φk k, Set.mem_iUnion.mpr ⟨hφkQ k,
        Set.mem_iUnion.mpr ⟨hσk k, hχsupp⟩⟩⟩
    · intro Fi hFi
      have hterm : |χ.val Fi - bProfile Fi| ≤ g χ := by
        rw [hg]
        exact Finset.single_le_sum (f := fun Fj => |χ.val Fj - bProfile Fj|)
          (fun j _ => abs_nonneg _) hFi
      have : |χ.val Fi - bProfile Fi| < ε := lt_of_le_of_lt hterm hχgood
      calc |χ.val Fi - ψ.val Fi| = |χ.val Fi - bProfile Fi| := by rw [hψval Fi]
        _ < ε := this
  · intro F
    rw [PositiveHomSpace.toPosHom_basisVector, hψval F, bProfile]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- **`thm:no-interior` (No interior pinning).**  Let `hc` be a hereditary class closed under deleting
edges, and `σ` a non-degenerate type.  If a `σ`-flag `F` is pinned to `c` on `S_σ` (i.e. `χ(F) = c`
for every `χ ∈ S_σ`), then `c ∈ {0,1}`.  Hence every pinning obstruction (`thm:pinning`) for such a
class is a boundary one. -/
theorem no_interior_pinning (hc : HeredClass) (hedc : EdgeDeletionClosed hc)
    (hnd : ∃ φ₀ : PositiveHom ∅ₜ,
      posHomPoint φ₀ ∈ Qσ (hc.constraintOf σ).forb0 ∧ φ₀ ⟨σ⟩₀ > 0)
    (F : FinFlag σ) (c : ℝ)
    (hpin : ∀ χ ∈ Sσ (hc.constraintOf σ), (PositiveHomSpace.toPosHom χ) ⟦basisVector F⟧ = c) :
    c = 0 ∨ c = 1 := by
  obtain ⟨ψ, hψS, hψbool⟩ := exists_boolean_point_in_Sσ hc hedc hnd
  have hc_eq : (PositiveHomSpace.toPosHom ψ) ⟦basisVector F⟧ = c := hpin ψ hψS
  rcases hψbool F with h | h <;> rw [hc_eq] at h
  · exact Or.inl h
  · exact Or.inr h

end FlagAlgebras.MetaTheory
