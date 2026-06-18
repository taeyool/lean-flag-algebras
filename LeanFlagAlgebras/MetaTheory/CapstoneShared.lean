import LeanFlagAlgebras.MetaTheory.RootingUniform
import LeanFlagAlgebras.MetaTheory.SupportClosure

/-! # The construction-agnostic capstone toolkit

The **construction-agnostic** measure-theoretic / topological infrastructure shared by the §5
(`CloneClosed`) and §6–§7 (`SubstitutionClosed`) root-plantability capstones (and reusable for the
§8+ developments).  None of it mentions any specific blow-up (`independentBlowup`/`blowupFlagSeq`/
`subBlowup`/`GraphClass`); it is pure flag-algebra/measure machinery factored out so that the
later capstones reuse it *without* depending on the §5 capstone `CloneClosed`.

It collects:

* the σ-rooting-measure-as-labelling-count identity `toProbMeasure_apply_eq_labeling_ratio`
  (the σ-rooting measure of a set of density profiles is the fraction of σ-labellings of the host
  whose induced profile lands in the set), built from `toProbMeasure_apply_eq_dnf_ratio`;
* closed coordinate cylinders `cyl`/`isClosed_cyl` in `FlagDensitySpace σ`;
* the finite-cylinder closure criterion `mem_closure_of_forall_finset_cylinder` (a point lies in
  the closure of a set provided every finite cylinder neighbourhood meets it);
* the asymptotic planted-estimate gap `rhoInf`;
* the σ-labelling/embedding counting isos `card_labelings_eq_card_embeddings`, `embeddingIsoCongr`,
  `card_labelings_eq_of_iso`, `transportLabeled`/`transportLabeled_iso`, and the
  isomorphism-invariance of flag density `flagDensity₁_respect_eqv`.
-/

open MeasureTheory Filter Topology
open SimpleGraph

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

attribute [local instance] Classical.propDecidable

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## A closure criterion via finite cylinders -/

/-- Continuity of the coordinate evaluation `χ ↦ χ.val F` on `PositiveHomSpace σ`. -/
theorem continuous_posHomSpace_coord (F : FinFlag σ) :
    Continuous (fun χ : PositiveHomSpace σ => χ.val F) :=
  (FinFlag.continuous F).comp continuous_subtype_val

/-- **Cylinder closure criterion.**  A point `ψ` lies in the closure of `A ⊆ PositiveHomSpace σ`
provided every finite cylinder neighborhood of `ψ` (an `ε`-box over a finite set `Fs` of
coordinates) meets `A`. -/
theorem mem_closure_of_forall_finset_cylinder {A : Set (PositiveHomSpace σ)}
    {ψ : PositiveHomSpace σ}
    (h : ∀ (Fs : Finset (FinFlag σ)) (ε : ℝ), 0 < ε →
        ∃ χ ∈ A, ∀ Fi ∈ Fs, |χ.val Fi - ψ.val Fi| < ε) :
    ψ ∈ closure A := by
  classical
  rw [mem_closure_iff_nhds]
  intro t ht
  -- Push the neighborhood `t` of `ψ` down to a product-cylinder neighborhood of `ψ.val`.
  rw [nhds_subtype, Filter.mem_comap] at ht
  obtain ⟨u, hu_nhds, hu_sub⟩ := ht
  rw [nhds_subtype, Filter.mem_comap] at hu_nhds
  obtain ⟨v, hv_nhds, hv_sub⟩ := hu_nhds
  rw [nhds_pi, Filter.mem_pi] at hv_nhds
  obtain ⟨I, hI_fin, w, hw_nhds, hw_sub⟩ := hv_nhds
  -- For each coordinate, a global `ε`-ball function (junk value `1` off `I`).
  have hball : ∀ Fi : FinFlag σ, ∃ ε : ℝ, 0 < ε ∧
      (Fi ∈ I → Set.Ioo ((ψ.val : FinFlag σ → ℝ) Fi - ε) ((ψ.val : FinFlag σ → ℝ) Fi + ε)
        ⊆ w Fi) := by
    intro Fi
    by_cases hFi : Fi ∈ I
    · obtain ⟨ε, hε, hball⟩ :=
        (nhds_basis_Ioo_pos ((ψ.val : FinFlag σ → ℝ) Fi)).mem_iff.mp (hw_nhds Fi)
      exact ⟨ε, hε, fun _ => hball⟩
    · exact ⟨1, by norm_num, fun hc => absurd hc hFi⟩
  choose εf hεf_pos hεf_sub using hball
  set Fs := hI_fin.toFinset with hFs
  -- Choose a common positive `ε'` bounding all the coordinate balls' radii.
  obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ∀ Fi ∈ Fs, ε' ≤ εf Fi := by
    rcases Fs.eq_empty_or_nonempty with he | hne
    · exact ⟨1, by norm_num, by simp [he]⟩
    · refine ⟨Fs.inf' hne εf, ?_, ?_⟩
      · exact (Finset.lt_inf'_iff hne).mpr (fun Fi _ => hεf_pos Fi)
      · intro Fi hFi
        exact Finset.inf'_le _ hFi
  -- Approximate `ψ` to within `ε'` on the coordinates `Fs`.
  obtain ⟨χ, hχA, hχ⟩ := h Fs ε' hε'_pos
  refine ⟨χ, ?_, hχA⟩
  apply hu_sub; apply hv_sub; apply hw_sub
  intro Fi hFi
  have hFiFs : Fi ∈ Fs := (Set.Finite.mem_toFinset hI_fin).mpr hFi
  apply hεf_sub Fi hFi
  rw [Set.mem_Ioo]
  have hlt : |χ.val Fi - ψ.val Fi| < εf Fi := lt_of_lt_of_le (hχ Fi hFiFs) (hε'_le Fi hFiFs)
  rw [abs_lt] at hlt
  show (ψ.val : FinFlag σ → ℝ) Fi - εf Fi < χ.val Fi ∧ χ.val Fi < (ψ.val : FinFlag σ → ℝ) Fi + εf Fi
  constructor <;> linarith [hlt.1, hlt.2]
/-! ## The σ-rooting measure as a uniform distribution over labelings -/

open Classical

/-- The `downwardNormalizingFactor` of a label extension `F'` of a size-`N` host is
`isomorphismCount F'.out` divided by the constant `N!/(N-n₀)!`. -/
private theorem dnf_eq_isomorphismCount_div (N : ℕ) (F' : FlagWithSize σ N) :
    (downwardNormalizingFactor F' : ℝ)
      = (isomorphismCount (Quotient.out F') : ℝ) / ((N.factorial / (N - n₀).factorial : ℕ) : ℝ) := by
  have h : downwardNormalizingFactor F'
      = downwardNormalizingFactor_labeledGraph (Quotient.out F') := by
    conv_lhs => rw [← Quotient.out_eq F']
    rfl
  rw [h]
  dsimp only [downwardNormalizingFactor_labeledGraph]
  push_cast
  rfl

/-- **Filtered fiberwise count.** For an iso-invariant (here: quotient-level) predicate `Q` on
size-`ℓ'` flags, the total `isomorphismCount` mass over the σ-label-extensions of `⟦F'⟧` that
satisfy `Q` equals the number of σ-labellings `H` of `F'.graph` with `Q ⟦H⟧`. -/
private theorem sum_isomorphismCount_labelExtensions_filtered (ℓ' : ℕ)
    (F' : LabeledGraph ∅ₜ (Fin ℓ')) (Q : FlagWithSize σ ℓ' → Prop) :
    ∑ G ∈ (labelExtensions (⟦F'⟧ : Flag ∅ₜ (Fin ℓ')) σ).filter (fun G => Q G),
        isomorphismCount G.out
      = (Finset.univ.filter
          (fun H : LabeledGraph σ (Fin ℓ') => H.graph = F'.graph ∧ Q (⟦H⟧ : FlagWithSize σ ℓ'))).card := by
  let S_F' : Finset (LabeledGraph σ (Fin ℓ')) :=
    Finset.univ.filter (fun H => H.graph = F'.graph ∧ Q (⟦H⟧ : FlagWithSize σ ℓ'))
  calc
    ∑ G ∈ (labelExtensions (⟦F'⟧ : Flag ∅ₜ (Fin ℓ')) σ).filter (fun G => Q G),
          isomorphismCount G.out
      = ∑ G ∈ (labelExtensions (⟦F'⟧ : Flag ∅ₜ (Fin ℓ')) σ).filter (fun G => Q G),
          {H ∈ S_F' | (⟦H⟧ : FlagWithSize σ ℓ') = G}.card := by
        apply Finset.sum_congr rfl
        intro G hGmem
        rw [Finset.mem_filter] at hGmem
        obtain ⟨hGF', hGQ⟩ := hGmem
        rcases Quotient.exists_rep G with ⟨G, rfl⟩
        dsimp only [labelExtensions] at hGF'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hGF'
        rw [unlabel_eq_iff_unlabeledGraph_eqv] at hGF'
        have hG_iso : (⟦G⟧ : FlagWithSize σ ℓ').out ∼f G := by
          show ⟦G⟧.out ≈ G
          exact Quotient.eq_mk_iff_out.mp rfl
        rw [isomorphismCount_respect_eqv hG_iso]
        dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph]
        let G' : LabeledGraph σ (Fin ℓ') := {
          graph := F'.graph
          type_embed := {
            toFun := hGF'.some.graph_iso ∘ G.type_embed
            inj' := by simp only [EmbeddingLike.comp_injective, RelEmbedding.injective]
            map_rel_iff' := by
              intro a b
              simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
              rw [type_embed_Adj_iff G]
              exact SimpleGraph.Iso.map_adj_iff (Nonempty.some hGF').graph_iso
          }
        }
        have hGG'_iso : G ∼f G' := by
          apply Nonempty.intro
          exact {
            graph_iso := by dsimp only [G']; exact hGF'.some.graph_iso
            type_preserve := by
              simp only [id_eq, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, G']
          }
        have hGG'_quot : (⟦G⟧ : FlagWithSize σ ℓ') = ⟦G'⟧ := Quotient.sound hGG'_iso
        calc
          _ = {H | G'.graph = H.graph ∧ G' ∼f H}.toFinset.card := by
            have := isomorphismCount_respect_eqv hGG'_iso
            dsimp only [isomorphismCount, isoLabeledGraphSetWithSameGraph] at this
            rw [this]; congr!
          _ = {H ∈ S_F' | (⟦H⟧ : FlagWithSize σ ℓ') = ⟦G⟧}.card := by
            congr 1
            ext H
            simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and, S_F']
            constructor
            · intro ⟨h_graph_eq, h_iso⟩
              dsimp only [G'] at h_graph_eq
              refine ⟨⟨h_graph_eq.symm, ?_⟩, ?_⟩
              · -- `⟦H⟧ = ⟦G⟧ = ⟦G'⟧` and `Q ⟦G⟧` holds
                have hHG : (⟦H⟧ : FlagWithSize σ ℓ') = ⟦G⟧ :=
                  Quotient.sound (h_iso.symm.trans hGG'_iso.symm)
                rw [hHG]; exact hGQ
              · simp only [Quotient.eq]
                exact h_iso.symm.trans hGG'_iso.symm
            · intro ⟨⟨h_graph_eq, _⟩, h_iso⟩
              simp only [Quotient.eq] at h_iso
              refine ⟨?_, ?_⟩
              · dsimp only [G']; rw [h_graph_eq]
              · exact hGG'_iso.symm.trans h_iso.symm
    _ = ∑ G ∈ S_F', (1 : ℕ) := by
        have h_quot_labelExt : ∀ H ∈ S_F',
            (⟦H⟧ : FlagWithSize σ ℓ') ∈ (labelExtensions (⟦F'⟧ : Flag ∅ₜ (Fin ℓ')) σ).filter
              (fun G => Q G) := by
          intro H hH
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, S_F'] at hH
          obtain ⟨hHgraph, hHQ⟩ := hH
          rw [Finset.mem_filter]
          refine ⟨?_, hHQ⟩
          simp only [labelExtensions, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [unlabel_eq_iff_unlabeledGraph_eqv]
          apply Nonempty.intro
          exact {
            graph_iso := by dsimp only [unlabeledGraph]; rw [hHgraph]
            type_preserve := List.ofFn_inj.mp rfl
          }
        rw [← Finset.sum_fiberwise_of_maps_to h_quot_labelExt (fun _ => (1 : ℕ))]
        apply Finset.sum_congr rfl
        intro H _
        rw [Finset.card_eq_sum_ones]
    _ = (Finset.univ.filter
          (fun H : LabeledGraph σ (Fin ℓ') => H.graph = F'.graph
            ∧ Q (⟦H⟧ : FlagWithSize σ ℓ'))).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- **Uniform-over-rootings count ratio.** The σ-rooting measure of a set `A` of density
profiles is the fraction of σ-labellings of the host graph whose induced density profile lands
in `A`. -/
theorem toProbMeasure_apply_eq_labeling_ratio (F : FinFlag ∅ₜ)
    (hF : flagDensity₁ σ.toEmptyTypeFlag F.2 > 0) (A : Set (FlagDensitySpace σ)) :
    ((F.toProbMeasure hF : Measure (FlagDensitySpace σ)) A).toReal
      = ((Finset.univ.filter (fun H : LabeledGraph σ (Fin F.1) =>
            H.graph = (Quotient.out F.2).graph ∧
            funFromFlagWithSizeToFlagDensitySpace σ F.1 (⟦H⟧ : FlagWithSize σ F.1) ∈ A)).card : ℝ)
        / ((Finset.univ.filter
            (fun H : LabeledGraph σ (Fin F.1) => H.graph = (Quotient.out F.2).graph)).card : ℝ) := by
  rw [toProbMeasure_apply_eq_dnf_ratio F hF A]
  set D : ℝ := ((F.1.factorial / (F.1 - n₀).factorial : ℕ) : ℝ) with hD
  set Fout : LabeledGraph ∅ₜ (Fin F.1) := Quotient.out F.2 with hFout
  have hFout_eq : (⟦Fout⟧ : Flag ∅ₜ (Fin F.1)) = F.2 := Quotient.out_eq F.2
  -- A general dnf-sum-over-a-filter identity: it is the filtered labeling count divided by `D`.
  have key : ∀ (P : FlagWithSize σ F.1 → Prop),
      (∑ F' ∈ (labelExtensions F.2 σ).filter (fun F' => P F'),
          (downwardNormalizingFactor F' : ℝ))
        = ((Finset.univ.filter (fun H : LabeledGraph σ (Fin F.1) =>
              H.graph = Fout.graph ∧ P (⟦H⟧ : FlagWithSize σ F.1))).card : ℝ) / D := by
    intro P
    -- rewrite each `dnf` as `isoCount/D`
    have hcongr : ∀ F' ∈ (labelExtensions F.2 σ).filter (fun F' => P F'),
        (downwardNormalizingFactor F' : ℝ)
          = (isomorphismCount (Quotient.out F') : ℝ) / D := by
      intro F' _; exact dnf_eq_isomorphismCount_div F.1 F'
    rw [Finset.sum_congr rfl hcongr, ← Finset.sum_div]
    congr 1
    rw [← Nat.cast_sum]
    congr 1
    -- reduce to the filtered fiberwise count lemma
    have := sum_isomorphismCount_labelExtensions_filtered (σ := σ) F.1 Fout P
    rw [hFout_eq] at this
    exact this
  have hnum := key (fun F' => funFromFlagWithSizeToFlagDensitySpace σ F.1 F' ∈ A)
  have hden := key (fun _ => True)
  simp only [Finset.filter_true, and_true] at hden
  have hDne : D ≠ 0 := by
    rw [hD]
    have hdvd : (F.1 - n₀).factorial ∣ F.1.factorial :=
      Nat.factorial_dvd_factorial (Nat.sub_le _ _)
    have hpos : 0 < F.1.factorial / (F.1 - n₀).factorial :=
      Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) hdvd) (Nat.factorial_pos _)
    exact_mod_cast hpos.ne'
  rw [hnum, hden, div_div_div_cancel_right₀ hDne]

/-! ## Closed coordinate-cylinders -/

/-- A closed coordinate-cylinder in `FlagDensitySpace σ`: profiles within `δ` of a center `b`
on a finite set `Fs` of coordinates. -/
def cyl (Fs : Finset (FinFlag σ)) (b : FinFlag σ → ℝ) (δ : ℝ) : Set (FlagDensitySpace σ) :=
  {a | ∀ Fi ∈ Fs, |a.val Fi - b Fi| ≤ δ}

theorem isClosed_cyl (Fs : Finset (FinFlag σ)) (b : FinFlag σ → ℝ) (δ : ℝ) :
    IsClosed (cyl Fs b δ) := by
  rw [cyl, Set.setOf_forall]
  refine isClosed_iInter fun Fi => ?_
  rw [Set.setOf_forall]
  refine isClosed_iInter fun _ => ?_
  exact isClosed_le ((continuous_abs.comp ((FinFlag.continuous Fi).sub continuous_const))) continuous_const

/-- The asymptotic planted-estimate gap `ρ_∞(n, r) = descFactorial(n−n₀, r) / n^r`, the limit of
the planted-estimate ratio as the (uniform) clone size grows. -/
noncomputable def rhoInf (n₀ n r : ℕ) : ℝ :=
  ((n - n₀).descFactorial r : ℝ) / ((n : ℝ) ^ r)

/-! ## Counting σ-labellings of a fixed host graph -/

/-- The σ-labellings of a fixed host graph `K` (labelled graphs with underlying graph `K`)
biject with the σ-embeddings `σ ↪g K`, via `H ↦ H.type_embed`. -/
def labelingEquivEmbedding {N : ℕ} (K : SimpleGraph (Fin N)) :
    {H : LabeledGraph σ (Fin N) // H.graph = K} ≃ (σ ↪g K) where
  toFun H := H.2 ▸ H.1.type_embed
  invFun e := ⟨⟨K, e⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨graph, te⟩, rfl⟩
    rfl
  right_inv := by
    intro e
    rfl

/-- The σ-labellings of a host graph `K`, as a `Finset`, has cardinality equal to the number of
σ-embeddings `σ ↪g K`. -/
theorem card_labelings_eq_card_embeddings {N : ℕ} (K : SimpleGraph (Fin N)) :
    (Finset.univ.filter (fun H : LabeledGraph σ (Fin N) => H.graph = K)).card
      = Fintype.card (σ ↪g K) := by
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  refine (Equiv.subtypeEquivRight ?_).trans (labelingEquivEmbedding K)
  intro H
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Post-composing with a graph isomorphism `K ≃g K'` transports σ-embeddings, giving a
bijection `(σ ↪g K) ≃ (σ ↪g K')`. -/
def embeddingIsoCongr {V W : Type} {K : SimpleGraph V} {K' : SimpleGraph W}
    (e : K ≃g K') : (σ ↪g K) ≃ (σ ↪g K') where
  toFun f := e.toEmbedding.comp f
  invFun f := e.symm.toEmbedding.comp f
  left_inv f := by
    ext x
    simp only [SimpleGraph.Embedding.coe_comp, Function.comp_apply, SimpleGraph.Iso.toEmbedding,
      RelIso.coe_toRelEmbedding, RelIso.symm_apply_apply]
  right_inv f := by
    ext x
    simp only [SimpleGraph.Embedding.coe_comp, Function.comp_apply, SimpleGraph.Iso.toEmbedding,
      RelIso.coe_toRelEmbedding, RelIso.apply_symm_apply]

/-- The number of σ-labellings of a host graph is invariant under graph isomorphism. -/
theorem card_labelings_eq_of_iso {N N' : ℕ} {K : SimpleGraph (Fin N)}
    {K' : SimpleGraph (Fin N')} (e : K ≃g K') :
    (Finset.univ.filter (fun H : LabeledGraph σ (Fin N) => H.graph = K)).card
      = (Finset.univ.filter (fun H : LabeledGraph σ (Fin N') => H.graph = K')).card := by
  rw [card_labelings_eq_card_embeddings, card_labelings_eq_card_embeddings]
  exact Fintype.card_congr (embeddingIsoCongr e)

/-- The density `flagDensity₁ Fi.2 ⟦G⟧` of a fixed flag in a host is invariant under a
flag-isomorphism `G₀ ≃f G₁` of the host (even across different vertex types). -/
theorem flagDensity₁_respect_eqv {U V : Type} [Fintype U] [DecidableEq U]
    [Fintype V] [DecidableEq V] (Fi : FinFlag σ)
    {G₀ : LabeledGraph σ U} {G₁ : LabeledGraph σ V} (φ : G₀ ≃f G₁) :
    flagDensity₁ Fi.2 (⟦G₀⟧ : Flag σ U) = flagDensity₁ Fi.2 (⟦G₁⟧ : Flag σ V) := by
  rcases Quotient.exists_rep Fi.2 with ⟨Frep, hF⟩
  rw [← hF]
  have e0 : flagDensity₁ (⟦Frep⟧ : Flag σ (Fin Fi.1)) (⟦G₀⟧ : Flag σ U)
      = subflagDensity (⟦Frep⟧ : Flag σ (Fin Fi.1)) (⟦G₀⟧ : Flag σ U) :=
    (subflagDensity_eq_flagListDensity _ _).symm
  have e1 : flagDensity₁ (⟦Frep⟧ : Flag σ (Fin Fi.1)) (⟦G₁⟧ : Flag σ V)
      = subflagDensity (⟦Frep⟧ : Flag σ (Fin Fi.1)) (⟦G₁⟧ : Flag σ V) :=
    (subflagDensity_eq_flagListDensity _ _).symm
  rw [e0, e1]
  show labeledGraphDensity Frep G₀ = labeledGraphDensity Frep G₁
  exact labeledGraphDensity_respect_eqv φ (LabeledGraphIso.refl (G := Frep))

/-- Transport a labelled graph along a graph isomorphism of its host (relabelling the vertex
type), giving an `≃f`-isomorphic labelled graph with the new host as underlying graph. -/
def transportLabeled {V W : Type} {G : LabeledGraph σ V} {K : SimpleGraph W}
    (e : G.graph ≃g K) : LabeledGraph σ W where
  graph := K
  type_embed := e.toEmbedding.comp G.type_embed

/-- The transport along `e` is `≃f`-isomorphic to the original (via `e`). -/
def transportLabeled_iso {V W : Type} {G : LabeledGraph σ V} {K : SimpleGraph W}
    (e : G.graph ≃g K) : G ≃f transportLabeled e where
  graph_iso := e
  type_preserve := rfl

end FlagAlgebras.MetaTheory
