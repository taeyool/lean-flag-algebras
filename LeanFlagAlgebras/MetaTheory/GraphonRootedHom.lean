import LeanFlagAlgebras.MetaTheory.GraphonRootedDensity

/-! # The rooted conditional homomorphism of a graphon

The assembly layer of the rooted transport: for a
graphon `W`, a two-vertex type `σ'`, and an **admissible** pinned pair `u v : I`
(`RootAdmissible`: positive root factor), the profile

`graphonRootedProfileFun W σ' u v F
   = (∑_{G std-rooted, ⟦G⟧ = F.2} unnormRootedDensity W _ G u v) / rootWeight W σ' u v`

is the conditional law of the `σ'`-rooted `W`-random graph given the root samples: the sum
ranges over the **standard-rooted** graphs in the class of `F` (`StdRootedBridge`), and
division by the root factor conditions on the root pair's adjacency.  The three structural
properties hold at every admissible pair —

* `oneProp`: the unit flag is the type itself on two vertices, of unnormalised density
  exactly `rootWeight` (`unnormRootedDensity_two`);
* `zeroSpaceProp`: the chain rule, by the extension partition
  (`unnormRootedDensity_extension_sum`) and averaging over root-fixing embeddings
  (`exists_rootfix_perm_comp_emb` + `unnormRootedDensity_comap_rootfix_perm` +
  `mkStdRooted_comap_rootfix_perm`), with the subset count given by
  `flagDensity₁_stdRooted` through the bridge `stdRooted_subset_iso_iff` /
  `exists_rootFixing_emb_range`;
* `mulProp`: multiplicativity, by the glued block product
  (`unnormRootedDensity_block_mul` — the shared root pair makes the `rootWeight`
  normalisation cancel exactly) and pair averaging (`exists_rootfix_perm_comp_emb_pair`),
  with the pair count from `flagDensity₂_eq_subset_count_div`;

so `positiveHomFromZeroSpaceOneMulProp` assembles the **rooted conditional homomorphism**
`graphonRootedHom W σ' u v h : PositiveHom σ'`.  Its joint measurability in `(u, v)`
(`measurable_graphonRootedProfileFun`) feeds the rooted-view measure of
`GraphonRootedMeasure.lean`.
-/

open MeasureTheory unitInterval Finset
open scoped Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

/-! ## The profile -/

/-- The rooted conditional profile: the probability that the `σ'`-rooted `W`-random graph on
`F.1` vertices (roots pinned at `u, v`, conditioned on the root adjacency) is isomorphic to
`F` as a rooted flag.  The sum ranges over the standard-rooted graphs in the class of `F`. -/
noncomputable def graphonRootedProfileFun (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    (F : FinFlag σ') : ℝ :=
  (∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin F.1) =>
      ∃ h : RootCompatible σ' (finFlag_size_ge_n₀ F) G,
        (⟦mkStdRooted σ' (finFlag_size_ge_n₀ F) G h⟧ : Flag σ' (Fin F.1)) = F.2),
      unnormRootedDensity W (finFlag_size_ge_n₀ F) G u v)
    / rootWeight W σ' u v

lemma graphonRootedProfileFun_nonneg (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    (F : FinFlag σ') : 0 ≤ graphonRootedProfileFun W σ' u v F := by
  unfold graphonRootedProfileFun
  exact div_nonneg
    (Finset.sum_nonneg fun G _ => unnormRootedDensity_nonneg W (finFlag_size_ge_n₀ F) G u v)
    (rootWeight_nonneg W σ' u v)

lemma graphonRootedProfileFun_le_one (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    (F : FinFlag σ') : graphonRootedProfileFun W σ' u v F ≤ 1 := by
  -- The filtered sum is bounded by the `RootCompatible` total `sum_unnormRootedDensity =
  -- rootWeight` (the profile filter implies `RootCompatible`); divide.  At inadmissible
  -- pairs the division is junk `0 ≤ 1`.
  unfold graphonRootedProfileFun
  set hn := finFlag_size_ge_n₀ F with hndef
  have hsub : (Finset.univ.filter (fun G : SimpleGraph (Fin F.1) =>
      ∃ h : RootCompatible σ' hn G,
        (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin F.1)) = F.2))
      ⊆ Finset.univ.filter (fun G : SimpleGraph (Fin F.1) => RootCompatible σ' hn G) := by
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG ⊢
    exact hG.1
  have hbound : (∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin F.1) =>
        ∃ h : RootCompatible σ' hn G,
          (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin F.1)) = F.2),
        unnormRootedDensity W hn G u v)
      ≤ ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin F.1) => RootCompatible σ' hn G),
        unnormRootedDensity W hn G u v :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun G _ _ => unnormRootedDensity_nonneg W hn G u v)
  rw [sum_unnormRootedDensity W σ' hn u v] at hbound
  rcases (rootWeight_nonneg W σ' u v).lt_or_eq with hpos | hz
  · exact (div_le_one hpos).mpr hbound
  · rw [← hz, div_zero]; norm_num

/-- Joint measurability of the profile in the pinned pair (feeds the rooted-view measure). -/
lemma measurable_graphonRootedProfileFun (W : Graphon) (σ' : FlagType (Fin 2))
    (F : FinFlag σ') :
    Measurable (fun z : I × I => graphonRootedProfileFun W σ' z.1 z.2 F) := by
  unfold graphonRootedProfileFun
  apply Measurable.div
  · exact Finset.measurable_sum _
      (fun G _ => measurable_unnormRootedDensity W (finFlag_size_ge_n₀ F) G)
  · exact measurable_rootWeight W σ'

/-! ## The three structural properties -/

theorem graphonRootedProfile_oneProp (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    (h : RootAdmissible W σ' u v) : oneProp (graphonRootedProfileFun W σ' u v) := by
  -- `(1 : FinFlag σ') = ⟨2, emptyFlag σ'⟩`; the only standard-rooted graph in the unit
  -- class is `σ'` itself (`rootCompatible_iff_comap_eq` at `n = 2`, where `castLE` is the
  -- identity), of unnormalised density `rootWeight` (`unnormRootedDensity_two`); divide.
  show graphonRootedProfileFun W σ' u v (1 : FinFlag σ') = 1
  unfold graphonRootedProfileFun
  set hn : 2 ≤ (1 : FinFlag σ').1 := finFlag_size_ge_n₀ (1 : FinFlag σ') with hndef
  have hcastLE : (Fin.castLE hn : Fin 2 → Fin (1 : FinFlag σ').1) = id := Fin.castLE_rfl 2
  have hfilter :
      (Finset.univ.filter (fun G : SimpleGraph (Fin (1 : FinFlag σ').1) =>
        ∃ hc : RootCompatible σ' hn G,
          (⟦mkStdRooted σ' hn G hc⟧ : Flag σ' (Fin (1 : FinFlag σ').1)) = (1 : FinFlag σ').2))
      = {σ'} := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [finFlag_one_snd]
    constructor
    · rintro ⟨hc, -⟩
      have hcomap := (rootCompatible_iff_comap_eq σ' hn G).mp hc
      rwa [hcastLE, SimpleGraph.comap_id] at hcomap
    · intro hGeq
      rw [hGeq]
      have hc : RootCompatible σ' hn σ' :=
        (rootCompatible_iff_comap_eq σ' hn σ').mpr (by rw [hcastLE, SimpleGraph.comap_id])
      refine ⟨hc, ?_⟩
      have hiso : mkStdRooted σ' hn σ' hc ∼f emptyLabeledGraph σ' := by
        refine ⟨SimpleGraph.Iso.refl, ?_⟩
        funext a
        show (Fin.castLE hn a : Fin (1 : FinFlag σ').1) = a
        rw [hcastLE]; rfl
      exact flagEqv.sound hiso
  rw [hfilter, Finset.sum_singleton]
  have htwo : unnormRootedDensity W hn σ' u v = rootWeight W σ' u v := by
    show unnormRootedDensity W (le_refl 2) σ' u v = adjWeight W (σ'.Adj 0 1) u v
    exact unnormRootedDensity_two W σ' u v
  rw [htwo]
  exact div_self (ne_of_gt h)

/-! ### Private machinery for `zeroSpaceProp` -/

/-- Root compatibility of the pullback along a root-fixing embedding is exactly root
compatibility of the host: both unfold to the same adjacency check at the images of the
roots. -/
private lemma rootCompatible_comap_rootFixing_iff (σ' : FlagType (Fin 2)) {n ℓ : ℕ}
    (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ) (j : Fin n ↪ Fin ℓ) (hj : RootFixing hn hℓ j)
    (H : SimpleGraph (Fin ℓ)) :
    RootCompatible σ' hn (H.comap ⇑j) ↔ RootCompatible σ' hℓ H := by
  constructor
  · intro hc a b
    have := hc a b
    rwa [SimpleGraph.comap_adj, hj a, hj b] at this
  · exact rootCompatible_comap_of_rootFixing hn hℓ j hj

/-- A sum of an indicator (`0`/constant `c`) over a `Fintype` is the count of the true set
times the constant (the same summation identity used in `GraphonHom`). -/
private lemma sum_ite_const_rooted {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (c : ℝ) : ∑ _x : α, (if P _x then c else 0) = (Finset.univ.filter P).card * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- A `LabeledGraphIso` forces the underlying vertex sets to have the same cardinality: a
graph isomorphism preserves `Fintype.card`. -/
private lemma card_eq_of_stdRooted_subset_iso (σ' : FlagType (Fin 2)) {n ℓ : ℕ}
    (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ) {Hp : SimpleGraph (Fin ℓ)} (hHp : RootCompatible σ' hℓ Hp)
    {G : SimpleGraph (Fin n)} (hG : RootCompatible σ' hn G)
    {S : Finset (Fin ℓ)}
    (h : (mkStdRooted σ' hℓ Hp hHp).type_verts ⊆ (↑S : Set (Fin ℓ)))
    (f : (LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHp) (↑S) h).coe
        ≃f mkStdRooted σ' hn G hG) : S.card = n := by
  have hsz : (LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHp) (↑S) h).coe.size
      = (mkStdRooted σ' hn G hG).size := labeledGraphIso_size_eq _ _ f
  rw [show (LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHp) (↑S) h).coe.size
        = (LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHp) (↑S) h).size from rfl,
      LabeledSubgraph.inducedLabeledSubgraph_size] at hsz
  rw [show (mkStdRooted σ' hn G hG).size = n from Fintype.card_fin n] at hsz
  simpa using hsz

/-- The number of `n`-element subsets of `Fin ℓ` containing both standard roots is
`C(ℓ−2, n−2)`: bijection with the `(n−2)`-subsets of the root-erased universe. -/
private lemma count_rootContaining_subsets {n ℓ : ℕ}
    (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ) (_hnℓ : n ≤ ℓ) :
    (Finset.univ.filter (fun S : Finset (Fin ℓ) =>
        ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)) ⊆ ↑S ∧ S.card = n)).card
      = (ℓ - 2).choose (n - 2) := by
  classical
  set roots : Finset (Fin ℓ) := {Fin.castLE hℓ 0, Fin.castLE hℓ 1} with hrootsdef
  have hne : Fin.castLE hℓ (0 : Fin 2) ≠ Fin.castLE hℓ (1 : Fin 2) := by
    simp only [ne_eq, Fin.castLE_inj]; decide
  have hrootscard : roots.card = 2 := by
    rw [hrootsdef, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have hcoe : (↑roots : Set (Fin ℓ)) = ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)) := by
    rw [hrootsdef]; simp
  have hfilter_eq : (Finset.univ.filter (fun S : Finset (Fin ℓ) =>
      ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)) ⊆ ↑S ∧ S.card = n))
      = Finset.univ.filter (fun S : Finset (Fin ℓ) => roots ⊆ S ∧ S.card = n) := by
    apply Finset.filter_congr
    intro S _
    rw [← hcoe, Finset.coe_subset]
  rw [hfilter_eq]
  have hbij : (Finset.univ.filter (fun S : Finset (Fin ℓ) => roots ⊆ S ∧ S.card = n)).card
      = (Finset.powersetCard (n - 2) (Finset.univ \ roots)).card := by
    apply Finset.card_bij' (fun S _ => S \ roots) (fun T _ => T ∪ roots)
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      obtain ⟨hsub, hcard⟩ := hS
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ S) (le_refl roots), ?_⟩
      rw [Finset.card_sdiff_of_subset hsub, hcard, hrootscard]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      obtain ⟨hsub, hcard⟩ := hT
      have hdisj : Disjoint T roots := Finset.disjoint_left.mpr (fun x hx hxr =>
        (Finset.mem_sdiff.mp (hsub hx)).2 hxr)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Finset.subset_union_right, ?_⟩
      rw [Finset.card_union_of_disjoint hdisj, hcard, hrootscard]
      omega
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact Finset.sdiff_union_of_subset hS.1
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      obtain ⟨hsub, -⟩ := hT
      have hdisj : Disjoint T roots := Finset.disjoint_left.mpr (fun x hx hxr =>
        (Finset.mem_sdiff.mp (hsub hx)).2 hxr)
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact h1
        · exact absurd h1 h2
      · intro hx
        exact ⟨Or.inl hx, Finset.disjoint_left.mp hdisj hx⟩
  rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ roots),
    Finset.card_univ, Fintype.card_fin, hrootscard]

/-- The total classifier of a graph on `Fin ℓ` into its standard-rooted flag class when
`RootCompatible`, or an arbitrary junk value otherwise (never consulted: it only makes the
fibrewise-regrouping classifier total). -/
private noncomputable def rootedClassOf (σ' : FlagType (Fin 2)) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (Hp : SimpleGraph (Fin ℓ)) : FlagWithSize σ' ℓ :=
  if hHp : RootCompatible σ' hℓ Hp then (⟦mkStdRooted σ' hℓ Hp hHp⟧ : Flag σ' (Fin ℓ))
  else (flagWithSize_inhabited σ' hℓ).default

private lemma rootedClassOf_eq_of_rootCompatible (σ' : FlagType (Fin 2)) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    {Hp : SimpleGraph (Fin ℓ)} (hHp : RootCompatible σ' hℓ Hp) :
    rootedClassOf σ' hℓ Hp = (⟦mkStdRooted σ' hℓ Hp hHp⟧ : Flag σ' (Fin ℓ)) := dif_pos hHp

/-- **Averaging over root-fixing embeddings**: the rooted analogue of
`sum_density_comap_embedding_eq` — the labelled sum picking out the fibre of the pullback
class over `F2` does not depend on which root-fixing embedding `Fin n ↪ Fin ℓ` is used to
restrict along. -/
private lemma sum_unnormRootedDensity_comap_rootfix_embedding_eq (W : Graphon)
    (σ' : FlagType (Fin 2)) (u v : I) {n ℓ : ℕ} (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ) (F2 : Flag σ' (Fin n))
    (j1 j2 : Fin n ↪ Fin ℓ) (hj1 : RootFixing hn hℓ j1) (hj2 : RootFixing hn hℓ j2) :
    (∑ Hp : SimpleGraph (Fin ℓ), if (∃ hc : RootCompatible σ' hn (Hp.comap ⇑j1),
          (⟦mkStdRooted σ' hn (Hp.comap ⇑j1) hc⟧ : Flag σ' (Fin n)) = F2)
        then unnormRootedDensity W hℓ Hp u v else 0)
      = ∑ Hp : SimpleGraph (Fin ℓ), if (∃ hc : RootCompatible σ' hn (Hp.comap ⇑j2),
          (⟦mkStdRooted σ' hn (Hp.comap ⇑j2) hc⟧ : Flag σ' (Fin n)) = F2)
        then unnormRootedDensity W hℓ Hp u v else 0 := by
  obtain ⟨π, hπ, hπroots⟩ := exists_rootfix_perm_comp_emb hn hℓ j2 j1 hj2 hj1
  have hcomp : (⇑π.symm ∘ ⇑j1 : Fin n → Fin ℓ) = ⇑j2 := by
    funext i
    show π.symm (j1 i) = j2 i
    rw [← hπ i, Equiv.symm_apply_apply]
  have hgraph : ∀ Hp : SimpleGraph (Fin ℓ), Hp.comap ⇑j2 = (Hp.comap ⇑π.symm).comap ⇑j1 := by
    intro Hp
    rw [SimpleGraph.comap_comap, hcomp]
  have hπroots_symm : ∀ a : Fin 2, π.symm (Fin.castLE hℓ a) = Fin.castLE hℓ a := by
    intro a
    calc π.symm (Fin.castLE hℓ a) = π.symm (π (Fin.castLE hℓ a)) := by rw [hπroots a]
      _ = Fin.castLE hℓ a := Equiv.symm_apply_apply π _
  have step1 : (∑ Hp : SimpleGraph (Fin ℓ), if (∃ hc : RootCompatible σ' hn (Hp.comap ⇑j2),
        (⟦mkStdRooted σ' hn (Hp.comap ⇑j2) hc⟧ : Flag σ' (Fin n)) = F2)
      then unnormRootedDensity W hℓ Hp u v else 0)
      = ∑ Hp : SimpleGraph (Fin ℓ),
        if (∃ hc : RootCompatible σ' hn ((Hp.comap ⇑π.symm).comap ⇑j1),
            (⟦mkStdRooted σ' hn ((Hp.comap ⇑π.symm).comap ⇑j1) hc⟧ : Flag σ' (Fin n)) = F2)
          then unnormRootedDensity W hℓ Hp u v else 0 :=
    Finset.sum_congr rfl (fun Hp _ => by rw [hgraph Hp])
  rw [step1]
  have step2 : (∑ Hp : SimpleGraph (Fin ℓ),
        if (∃ hc : RootCompatible σ' hn ((Hp.comap ⇑π.symm).comap ⇑j1),
            (⟦mkStdRooted σ' hn ((Hp.comap ⇑π.symm).comap ⇑j1) hc⟧ : Flag σ' (Fin n)) = F2)
          then unnormRootedDensity W hℓ Hp u v else 0)
      = ∑ Hp : SimpleGraph (Fin ℓ),
        if (∃ hc : RootCompatible σ' hn ((Hp.comap ⇑π.symm).comap ⇑j1),
            (⟦mkStdRooted σ' hn ((Hp.comap ⇑π.symm).comap ⇑j1) hc⟧ : Flag σ' (Fin n)) = F2)
          then unnormRootedDensity W hℓ (Hp.comap ⇑π.symm) u v else 0 :=
    Finset.sum_congr rfl (fun Hp _ => by
      rw [← unnormRootedDensity_comap_rootfix_perm W hℓ π.symm hπroots_symm Hp u v])
  rw [step2]
  exact (Equiv.sum_comp (graphComapEquiv π.symm)
    (fun Hp' => if (∃ hc : RootCompatible σ' hn (Hp'.comap ⇑j1),
        (⟦mkStdRooted σ' hn (Hp'.comap ⇑j1) hc⟧ : Flag σ' (Fin n)) = F2)
      then unnormRootedDensity W hℓ Hp' u v else 0)).symm

/-- **The rooted chain-rule core**: the rooted analogue of `graphonProfile_zeroSpace_aux`. -/
private lemma graphonRootedProfile_zeroSpace_aux (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    {n ℓ : ℕ} (hn : 2 ≤ n) (hnℓ : n ≤ ℓ) (F2 : Flag σ' (Fin n)) :
    (∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
        ∃ h : RootCompatible σ' hn G, (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin n)) = F2),
        unnormRootedDensity W hn G u v)
      = ∑ Gℓ : FlagWithSize σ' ℓ, (flagDensity₁ F2 Gℓ : ℝ) *
          (∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin ℓ) =>
              ∃ h : RootCompatible σ' (hn.trans hnℓ) H,
                (⟦mkStdRooted σ' (hn.trans hnℓ) H h⟧ : Flag σ' (Fin ℓ)) = Gℓ),
              unnormRootedDensity W (hn.trans hnℓ) H u v) := by
  set hℓ := hn.trans hnℓ with hℓdef
  obtain ⟨Grep, hGrep, hGrepEq⟩ := exists_stdRooted_rep hn F2
  set sVal : ℝ := ∑ Hp : SimpleGraph (Fin ℓ), if (∃ hc : RootCompatible σ' hn (Hp.comap (Fin.castLE hnℓ)),
      (⟦mkStdRooted σ' hn (Hp.comap (Fin.castLE hnℓ)) hc⟧ : Flag σ' (Fin n)) = F2)
    then unnormRootedDensity W hℓ Hp u v else 0 with hsValdef
  have hstep1 : (∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
        ∃ h : RootCompatible σ' hn G, (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin n)) = F2),
        unnormRootedDensity W hn G u v) = sVal := by
    rw [hsValdef]
    rw [Finset.sum_congr rfl (fun G _ => unnormRootedDensity_extension_sum W hn hnℓ G u v)]
    rw [show (∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => ∃ h : RootCompatible σ' hn G,
          (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin n)) = F2),
        ∑ Hp ∈ Finset.univ.filter (fun Hp : SimpleGraph (Fin ℓ) => Hp.comap (Fin.castLE hnℓ) = G),
          unnormRootedDensity W hℓ Hp u v)
        = ∑ Hp ∈ Finset.univ.filter (fun Hp : SimpleGraph (Fin ℓ) =>
            Hp.comap (Fin.castLE hnℓ) ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) =>
              ∃ h : RootCompatible σ' hn G, (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin n)) = F2)),
            unnormRootedDensity W hℓ Hp u v
        from Finset.sum_fiberwise_eq_sum_filter _ _ _ _]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext Hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro Hp _; rfl
  rw [hstep1]
  have hchoose_pos : 0 < (ℓ - 2).choose (n - 2) := Nat.choose_pos (by omega)
  have hchoose_ne : ((ℓ - 2).choose (n - 2) : ℝ) ≠ 0 := by exact_mod_cast hchoose_pos.ne'
  have hT_S : ∀ S : Finset (Fin ℓ),
      (∑ Hp : SimpleGraph (Fin ℓ), if (∃ hHp : RootCompatible σ' hℓ Hp,
            ∃ h' : (mkStdRooted σ' hℓ Hp hHp).type_verts ⊆ (↑S : Set (Fin ℓ)),
              Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHp) (↑S) h').coe
                ≃f mkStdRooted σ' hn Grep hGrep))
          then unnormRootedDensity W hℓ Hp u v else 0)
        = if (({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)) ⊆ ↑S ∧ S.card = n)
          then sVal else 0 := by
    intro S
    by_cases hcond : (({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)) ⊆ ↑S) ∧ S.card = n
    · rw [if_pos hcond]
      obtain ⟨hroots, hcard⟩ := hcond
      obtain ⟨j, hj, hSrange⟩ := exists_rootFixing_emb_range hn hℓ S hroots hcard
      have hconv : (∑ Hp : SimpleGraph (Fin ℓ), if (∃ hHp : RootCompatible σ' hℓ Hp,
            ∃ h' : (mkStdRooted σ' hℓ Hp hHp).type_verts ⊆ (↑S : Set (Fin ℓ)),
              Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHp) (↑S) h').coe
                ≃f mkStdRooted σ' hn Grep hGrep))
          then unnormRootedDensity W hℓ Hp u v else 0)
        = ∑ Hp : SimpleGraph (Fin ℓ), if (∃ hc : RootCompatible σ' hn (Hp.comap ⇑j),
            (⟦mkStdRooted σ' hn (Hp.comap ⇑j) hc⟧ : Flag σ' (Fin n)) = F2)
          then unnormRootedDensity W hℓ Hp u v else 0 := by
        apply Finset.sum_congr rfl
        intro Hp _
        congr 1
        rw [eq_iff_iff]
        constructor
        · rintro ⟨hHp, h', e⟩
          refine ⟨rootCompatible_comap_of_rootFixing hn hℓ j hj hHp, ?_⟩
          rw [← hGrepEq]
          exact (stdRooted_subset_iso_iff hn hℓ Hp hHp Grep hGrep j hj S hSrange).mp ⟨h', e⟩
        · rintro ⟨hc, e⟩
          have hHp : RootCompatible σ' hℓ Hp :=
            (rootCompatible_comap_rootFixing_iff σ' hn hℓ j hj Hp).mp hc
          refine ⟨hHp, ?_⟩
          apply (stdRooted_subset_iso_iff hn hℓ Hp hHp Grep hGrep j hj S hSrange).mpr
          rw [hGrepEq]
          exact e
      rw [hconv, hsValdef]
      exact sum_unnormRootedDensity_comap_rootfix_embedding_eq W σ' u v hn hℓ F2 j
        (Fin.castLEEmb hnℓ) hj (rootFixing_castLE hn hℓ hnℓ)
    · rw [if_neg hcond]
      apply Finset.sum_eq_zero
      intro Hp _
      apply if_neg
      rintro ⟨hHp, h', e⟩
      apply hcond
      refine ⟨?_, ?_⟩
      · rw [← mkStdRooted_type_verts hℓ Hp hHp]; exact h'
      · exact card_eq_of_stdRooted_subset_iso σ' hn hℓ hHp hGrep h' (Classical.choice e)
  have hT1 : (∑ S : Finset (Fin ℓ), ∑ Hp : SimpleGraph (Fin ℓ),
        (if (∃ hHp : RootCompatible σ' hℓ Hp,
            ∃ h' : (mkStdRooted σ' hℓ Hp hHp).type_verts ⊆ (↑S : Set (Fin ℓ)),
              Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHp) (↑S) h').coe
                ≃f mkStdRooted σ' hn Grep hGrep))
          then unnormRootedDensity W hℓ Hp u v else 0))
      = ((ℓ - 2).choose (n - 2) : ℝ) * sVal := by
    rw [Finset.sum_congr rfl (fun S _ => hT_S S), sum_ite_const_rooted,
      count_rootContaining_subsets hn hℓ hnℓ]
  have hT2 : (∑ S : Finset (Fin ℓ), ∑ Hp : SimpleGraph (Fin ℓ),
        (if (∃ hHp : RootCompatible σ' hℓ Hp,
            ∃ h' : (mkStdRooted σ' hℓ Hp hHp).type_verts ⊆ (↑S : Set (Fin ℓ)),
              Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHp) (↑S) h').coe
                ≃f mkStdRooted σ' hn Grep hGrep))
          then unnormRootedDensity W hℓ Hp u v else 0))
      = ((ℓ - 2).choose (n - 2) : ℝ) * ∑ Hp ∈ Finset.univ.filter (fun Hp : SimpleGraph (Fin ℓ) =>
            RootCompatible σ' hℓ Hp),
          (flagDensity₁ F2 (rootedClassOf σ' hℓ Hp) : ℝ) * unnormRootedDensity W hℓ Hp u v := by
    rw [Finset.sum_comm]
    have hstep : (∑ Hp : SimpleGraph (Fin ℓ), ∑ S : Finset (Fin ℓ),
          (if (∃ hHp : RootCompatible σ' hℓ Hp,
              ∃ h' : (mkStdRooted σ' hℓ Hp hHp).type_verts ⊆ (↑S : Set (Fin ℓ)),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHp) (↑S) h').coe
                  ≃f mkStdRooted σ' hn Grep hGrep))
            then unnormRootedDensity W hℓ Hp u v else 0))
        = ∑ Hp ∈ Finset.univ.filter (fun Hp : SimpleGraph (Fin ℓ) => RootCompatible σ' hℓ Hp),
            ∑ S : Finset (Fin ℓ),
            (if (∃ hHp : RootCompatible σ' hℓ Hp,
                ∃ h' : (mkStdRooted σ' hℓ Hp hHp).type_verts ⊆ (↑S : Set (Fin ℓ)),
                  Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHp) (↑S) h').coe
                    ≃f mkStdRooted σ' hn Grep hGrep))
              then unnormRootedDensity W hℓ Hp u v else 0) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro Hp _ hHp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hHp
      apply Finset.sum_eq_zero
      intro S _
      apply if_neg
      rintro ⟨hHp', -⟩
      exact hHp hHp'
    rw [hstep, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Hp hHpmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hHpmem
    have hfilter_eq : (Finset.univ.filter (fun S : Finset (Fin ℓ) =>
          ∃ hHp' : RootCompatible σ' hℓ Hp,
            ∃ h' : (mkStdRooted σ' hℓ Hp hHp').type_verts ⊆ (↑S : Set (Fin ℓ)),
              Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHp') (↑S) h').coe
                ≃f mkStdRooted σ' hn Grep hGrep)))
        = Finset.univ.filter (fun S : Finset (Fin ℓ) =>
          ∃ h' : (mkStdRooted σ' hℓ Hp hHpmem).type_verts ⊆ (↑S : Set (Fin ℓ)),
            Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHpmem) (↑S) h').coe
              ≃f mkStdRooted σ' hn Grep hGrep)) := by
      apply Finset.filter_congr
      intro S _
      constructor
      · rintro ⟨_hHp', h', e⟩
        exact ⟨h', e⟩
      · rintro ⟨h', e⟩
        exact ⟨hHpmem, h', e⟩
    rw [sum_ite_const_rooted, hfilter_eq]
    have hden := flagDensity₁_stdRooted hn hℓ Grep hGrep Hp hHpmem
    rw [hGrepEq] at hden
    have hcount : ((Finset.univ.filter (fun S : Finset (Fin ℓ) =>
          ∃ h' : (mkStdRooted σ' hℓ Hp hHpmem).type_verts ⊆ (↑S : Set (Fin ℓ)),
            Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHpmem) (↑S) h').coe
              ≃f mkStdRooted σ' hn Grep hGrep))).card : ℚ)
        = flagDensity₁ F2 (⟦mkStdRooted σ' hℓ Hp hHpmem⟧) * ((ℓ - 2).choose (n - 2) : ℚ) := by
      rw [hden]; field_simp
    have hcount_real : ((Finset.univ.filter (fun S : Finset (Fin ℓ) =>
          ∃ h' : (mkStdRooted σ' hℓ Hp hHpmem).type_verts ⊆ (↑S : Set (Fin ℓ)),
            Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ Hp hHpmem) (↑S) h').coe
              ≃f mkStdRooted σ' hn Grep hGrep))).card : ℝ)
        = (flagDensity₁ F2 (⟦mkStdRooted σ' hℓ Hp hHpmem⟧) : ℝ) * ((ℓ - 2).choose (n - 2) : ℝ) := by
      exact_mod_cast hcount
    rw [hcount_real, rootedClassOf_eq_of_rootCompatible σ' hℓ hHpmem]
    ring
  have hsVal_eq : sVal
      = ∑ Hp ∈ Finset.univ.filter (fun Hp : SimpleGraph (Fin ℓ) => RootCompatible σ' hℓ Hp),
        (flagDensity₁ F2 (rootedClassOf σ' hℓ Hp) : ℝ) * unnormRootedDensity W hℓ Hp u v :=
    mul_left_cancel₀ hchoose_ne (hT1.symm.trans hT2)
  rw [hsVal_eq]
  rw [← Finset.sum_fiberwise
      (Finset.univ.filter (fun Hp : SimpleGraph (Fin ℓ) => RootCompatible σ' hℓ Hp))
      (rootedClassOf σ' hℓ)
      (fun Hp => (flagDensity₁ F2 (rootedClassOf σ' hℓ Hp) : ℝ) * unnormRootedDensity W hℓ Hp u v)]
  apply Finset.sum_congr rfl
  intro Gℓ _
  have hrw : ∀ Hp ∈ (Finset.univ.filter (fun Hp : SimpleGraph (Fin ℓ) => RootCompatible σ' hℓ Hp)).filter
      (fun Hp => rootedClassOf σ' hℓ Hp = Gℓ),
      (flagDensity₁ F2 (rootedClassOf σ' hℓ Hp) : ℝ) * unnormRootedDensity W hℓ Hp u v
        = (flagDensity₁ F2 Gℓ : ℝ) * unnormRootedDensity W hℓ Hp u v := by
    intro Hp hHp
    rw [(Finset.mem_filter.mp hHp).2]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr
  · ext Hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hHp, hcl⟩
      exact ⟨hHp, by rw [← rootedClassOf_eq_of_rootCompatible σ' hℓ hHp]; exact hcl⟩
    · rintro ⟨hHp, hcl⟩
      exact ⟨hHp, by rw [rootedClassOf_eq_of_rootCompatible σ' hℓ hHp]; exact hcl⟩
  · intro Hp _; rfl

theorem graphonRootedProfile_zeroSpaceProp (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    (_h : RootAdmissible W σ' u v) : zeroSpaceProp (graphonRootedProfileFun W σ' u v) := by
  -- The chain rule, via the rooted extension-partition + root-fixing subset-averaging scheme:
  -- extensions `unnormRootedDensity_extension_sum`; averaging
  -- `exists_rootfix_perm_comp_emb` + `unnormRootedDensity_comap_rootfix_perm` +
  -- `mkStdRooted_comap_rootfix_perm`; subsets ↔ embeddings `exists_rootFixing_emb_range` /
  -- `stdRooted_subset_iso_iff`; count `flagDensity₁_stdRooted`, denominator
  -- `C(ℓ−2, n−2)` = the number of root-containing `n`-subsets; class regrouping
  -- `exists_stdRooted_rep` + `Finset.sum_fiberwise`-style reindexing.  The `rootWeight`
  -- normalisation passes through the (linear) chain rule untouched.
  intro F ℓ hFl
  show graphonRootedProfileFun W σ' u v F
      = ∑ G : FlagWithSize σ' ℓ, (flagDensity₁ F.2 G : ℝ) * graphonRootedProfileFun W σ' u v ⟨ℓ, G⟩
  have hcore := graphonRootedProfile_zeroSpace_aux W σ' u v (finFlag_size_ge_n₀ F) hFl F.2
  unfold graphonRootedProfileFun
  rw [hcore, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro G _
  rw [mul_div_assoc]

/-! ### Private machinery for `mulProp` -/

/-- Regroup a triple sum (two labels + the underlying index) picking out the fibre of a pair
`(g1, g2)` over `t1 × t2` into a single filtered sum (the same regrouping identity used in
`GraphonHom`). -/
private lemma sum_double_fiberwise {ι κ₁ κ₂ : Type*} [Fintype ι] [DecidableEq κ₁] [DecidableEq κ₂]
    (t₁ : Finset κ₁) (t₂ : Finset κ₂) (g₁ : ι → κ₁) (g₂ : ι → κ₂) (f : ι → ℝ) :
    (∑ j₁ ∈ t₁, ∑ j₂ ∈ t₂,
        ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => g₁ i = j₁ ∧ g₂ i = j₂), f i)
      = ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => g₁ i ∈ t₁ ∧ g₂ i ∈ t₂), f i := by
  have step1 : ∀ j₁ : κ₁,
      (∑ j₂ ∈ t₂, ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => g₁ i = j₁ ∧ g₂ i = j₂), f i)
      = ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => g₁ i = j₁ ∧ g₂ i ∈ t₂), f i := by
    intro j₁
    have hfilt : ∀ j₂ : κ₂, (Finset.univ : Finset ι).filter (fun i => g₁ i = j₁ ∧ g₂ i = j₂)
        = ((Finset.univ : Finset ι).filter (fun i => g₁ i = j₁)).filter (fun i => g₂ i = j₂) :=
      fun j₂ => (Finset.filter_filter _ _ _).symm
    simp_rw [hfilt]
    rw [Finset.sum_fiberwise_eq_sum_filter, Finset.filter_filter]
  rw [Finset.sum_congr rfl (fun j₁ _ => step1 j₁)]
  have hswap : ∀ j₁ : κ₁, (Finset.univ : Finset ι).filter (fun i => g₁ i = j₁ ∧ g₂ i ∈ t₂)
      = ((Finset.univ : Finset ι).filter (fun i => g₂ i ∈ t₂)).filter (fun i => g₁ i = j₁) := by
    intro j₁
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun i _ => and_comm)
  simp_rw [hswap]
  rw [Finset.sum_fiberwise_eq_sum_filter, Finset.filter_filter]
  exact Finset.sum_congr (Finset.filter_congr (fun i _ => and_comm)) (fun _ _ => rfl)

/-- The two standard-rooted vertices of `Fin ℓ`, as a `Finset`. -/
private def rootFinset {ℓ : ℕ} (hℓ : 2 ≤ ℓ) : Finset (Fin ℓ) :=
  {Fin.castLE hℓ 0, Fin.castLE hℓ 1}

private lemma rootFinset_coe {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (↑(rootFinset hℓ) : Set (Fin ℓ)) = ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)) := by
  simp [rootFinset]

private lemma rootFinset_card {ℓ : ℕ} (hℓ : 2 ≤ ℓ) : (rootFinset hℓ).card = 2 := by
  have hne : Fin.castLE hℓ (0 : Fin 2) ≠ Fin.castLE hℓ (1 : Fin 2) := by
    simp only [ne_eq, Fin.castLE_inj]; decide
  rw [rootFinset, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

/-- `roots ⊆ range j` for any root-fixing embedding `j`: each root is the image of the
corresponding root of the domain. -/
private lemma roots_subset_range_of_rootFixing {n' ℓ : ℕ} (hn' : 2 ≤ n') (hℓ : 2 ≤ ℓ)
    (j : Fin n' ↪ Fin ℓ) (hj : RootFixing hn' hℓ j) :
    ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)) ⊆ Set.range ⇑j := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact ⟨Fin.castLE hn' 0, hj 0⟩
  · exact ⟨Fin.castLE hn' 1, hj 1⟩

/-- `multinomialCoefficient ![a, b] (a + b) = (a + b).choose a`, the same reduction used in
`EmptyTypeGraphBridge.flagDensity₂_graphFlag`. -/
private lemma multinomialCoefficient_two_eq_choose (a b : ℕ) :
    multinomialCoefficient ![a, b] (a + b) = (a + b).choose a := by
  rw [multinomialCoefficient_eq_choose_mul_multinomial]
  have hsum : (∑ x, (![a, b] : Fin 2 → ℕ) x) = a + b := by simp [Fin.sum_univ_two]
  rw [hsum, Nat.choose_self, one_mul]
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [huniv, Nat.binomial_eq_choose (by decide : (0 : Fin 2) ≠ 1)]
  simp

/-- **Pair-flag density as a subset-pair count for standard-rooted flags** (the pair analogue
of `flagDensity₁_stdRooted`). -/
private lemma flagDensity₂_stdRooted (σ' : FlagType (Fin 2)) {n₁ n₂ ℓ : ℕ}
    (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (hℓ : 2 ≤ ℓ)
    (G₁ : SimpleGraph (Fin n₁)) (hG₁ : RootCompatible σ' hn₁ G₁)
    (G₂ : SimpleGraph (Fin n₂)) (hG₂ : RootCompatible σ' hn₂ G₂)
    (H : SimpleGraph (Fin ℓ)) (hH : RootCompatible σ' hℓ H) :
    flagDensity₂ (⟦mkStdRooted σ' hn₁ G₁ hG₁⟧ : Flag σ' (Fin n₁))
        (⟦mkStdRooted σ' hn₂ G₂ hG₂⟧ : Flag σ' (Fin n₂))
        (⟦mkStdRooted σ' hℓ H hH⟧ : Flag σ' (Fin ℓ))
      = ((Finset.univ.filter (fun P : Finset (Fin ℓ) × Finset (Fin ℓ) =>
          IsInducedPairOn (mkStdRooted σ' hn₁ G₁ hG₁) (mkStdRooted σ' hn₂ G₂ hG₂)
            (mkStdRooted σ' hℓ H hH) P)).card : ℚ)
        / (multinomialCoefficient ![n₁ - 2, n₂ - 2] (ℓ - 2)) := by
  rw [flagDensity₂_eq_subset_count_div]
  simp only [LabeledGraph.size, Fintype.card_fin, flagTypeFin2_size]

/-- **Averaging over pairs of root-fixing embeddings**: the pair analogue of
`sum_unnormRootedDensity_comap_rootfix_embedding_eq`. -/
private lemma sum_unnormRootedDensity_comap_rootfix_pair_embedding_eq (W : Graphon)
    (σ' : FlagType (Fin 2)) (u v : I) {n₁ n₂ ℓ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (hℓ : 2 ≤ ℓ)
    (F₁ : Flag σ' (Fin n₁)) (F₂ : Flag σ' (Fin n₂))
    (j₁ k₁ : Fin n₁ ↪ Fin ℓ) (j₂ k₂ : Fin n₂ ↪ Fin ℓ)
    (hj₁ : RootFixing hn₁ hℓ j₁) (hk₁ : RootFixing hn₁ hℓ k₁)
    (hj₂ : RootFixing hn₂ hℓ j₂) (hk₂ : RootFixing hn₂ hℓ k₂)
    (hj : Set.range ⇑j₁ ∩ Set.range ⇑j₂ = ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ)))
    (hk : Set.range ⇑k₁ ∩ Set.range ⇑k₂ = ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin ℓ))) :
    (∑ H : SimpleGraph (Fin ℓ), if (∃ hc₁ : RootCompatible σ' hn₁ (H.comap ⇑k₁),
          (⟦mkStdRooted σ' hn₁ (H.comap ⇑k₁) hc₁⟧ : Flag σ' (Fin n₁)) = F₁)
        ∧ (∃ hc₂ : RootCompatible σ' hn₂ (H.comap ⇑k₂),
          (⟦mkStdRooted σ' hn₂ (H.comap ⇑k₂) hc₂⟧ : Flag σ' (Fin n₂)) = F₂)
        then unnormRootedDensity W hℓ H u v else 0)
      = ∑ H : SimpleGraph (Fin ℓ), if (∃ hc₁ : RootCompatible σ' hn₁ (H.comap ⇑j₁),
          (⟦mkStdRooted σ' hn₁ (H.comap ⇑j₁) hc₁⟧ : Flag σ' (Fin n₁)) = F₁)
        ∧ (∃ hc₂ : RootCompatible σ' hn₂ (H.comap ⇑j₂),
          (⟦mkStdRooted σ' hn₂ (H.comap ⇑j₂) hc₂⟧ : Flag σ' (Fin n₂)) = F₂)
        then unnormRootedDensity W hℓ H u v else 0 := by
  obtain ⟨π, hπ1, hπ2⟩ := exists_rootfix_perm_comp_emb_pair hn₁ hn₂ hℓ k₁ j₁ k₂ j₂ hk₁ hj₁ hk₂ hj₂ hk hj
  have hcomp1 : (⇑π.symm ∘ ⇑j₁ : Fin n₁ → Fin ℓ) = ⇑k₁ := by
    funext i; show π.symm (j₁ i) = k₁ i; rw [← hπ1 i, Equiv.symm_apply_apply]
  have hcomp2 : (⇑π.symm ∘ ⇑j₂ : Fin n₂ → Fin ℓ) = ⇑k₂ := by
    funext i; show π.symm (j₂ i) = k₂ i; rw [← hπ2 i, Equiv.symm_apply_apply]
  have hgraph1 : ∀ H : SimpleGraph (Fin ℓ), H.comap ⇑k₁ = (H.comap ⇑π.symm).comap ⇑j₁ := by
    intro H; rw [SimpleGraph.comap_comap, hcomp1]
  have hgraph2 : ∀ H : SimpleGraph (Fin ℓ), H.comap ⇑k₂ = (H.comap ⇑π.symm).comap ⇑j₂ := by
    intro H; rw [SimpleGraph.comap_comap, hcomp2]
  have hπroots : ∀ a : Fin 2, π (Fin.castLE hℓ a) = Fin.castLE hℓ a := by
    intro a
    calc π (Fin.castLE hℓ a) = π (k₁ (Fin.castLE hn₁ a)) := by rw [hk₁ a]
      _ = j₁ (Fin.castLE hn₁ a) := hπ1 (Fin.castLE hn₁ a)
      _ = Fin.castLE hℓ a := hj₁ a
  have hπroots_symm : ∀ a : Fin 2, π.symm (Fin.castLE hℓ a) = Fin.castLE hℓ a := by
    intro a
    calc π.symm (Fin.castLE hℓ a) = π.symm (π (Fin.castLE hℓ a)) := by rw [hπroots a]
      _ = Fin.castLE hℓ a := Equiv.symm_apply_apply π _
  have step1 : (∑ H : SimpleGraph (Fin ℓ), if (∃ hc₁ : RootCompatible σ' hn₁ (H.comap ⇑k₁),
          (⟦mkStdRooted σ' hn₁ (H.comap ⇑k₁) hc₁⟧ : Flag σ' (Fin n₁)) = F₁)
        ∧ (∃ hc₂ : RootCompatible σ' hn₂ (H.comap ⇑k₂),
          (⟦mkStdRooted σ' hn₂ (H.comap ⇑k₂) hc₂⟧ : Flag σ' (Fin n₂)) = F₂)
        then unnormRootedDensity W hℓ H u v else 0)
      = ∑ H : SimpleGraph (Fin ℓ),
        if (∃ hc₁ : RootCompatible σ' hn₁ ((H.comap ⇑π.symm).comap ⇑j₁),
              (⟦mkStdRooted σ' hn₁ ((H.comap ⇑π.symm).comap ⇑j₁) hc₁⟧ : Flag σ' (Fin n₁)) = F₁)
          ∧ (∃ hc₂ : RootCompatible σ' hn₂ ((H.comap ⇑π.symm).comap ⇑j₂),
              (⟦mkStdRooted σ' hn₂ ((H.comap ⇑π.symm).comap ⇑j₂) hc₂⟧ : Flag σ' (Fin n₂)) = F₂)
          then unnormRootedDensity W hℓ H u v else 0 :=
    Finset.sum_congr rfl (fun H _ => by rw [hgraph1 H, hgraph2 H])
  rw [step1]
  have step2 : (∑ H : SimpleGraph (Fin ℓ),
        if (∃ hc₁ : RootCompatible σ' hn₁ ((H.comap ⇑π.symm).comap ⇑j₁),
              (⟦mkStdRooted σ' hn₁ ((H.comap ⇑π.symm).comap ⇑j₁) hc₁⟧ : Flag σ' (Fin n₁)) = F₁)
          ∧ (∃ hc₂ : RootCompatible σ' hn₂ ((H.comap ⇑π.symm).comap ⇑j₂),
              (⟦mkStdRooted σ' hn₂ ((H.comap ⇑π.symm).comap ⇑j₂) hc₂⟧ : Flag σ' (Fin n₂)) = F₂)
          then unnormRootedDensity W hℓ H u v else 0)
      = ∑ H : SimpleGraph (Fin ℓ),
        if (∃ hc₁ : RootCompatible σ' hn₁ ((H.comap ⇑π.symm).comap ⇑j₁),
              (⟦mkStdRooted σ' hn₁ ((H.comap ⇑π.symm).comap ⇑j₁) hc₁⟧ : Flag σ' (Fin n₁)) = F₁)
          ∧ (∃ hc₂ : RootCompatible σ' hn₂ ((H.comap ⇑π.symm).comap ⇑j₂),
              (⟦mkStdRooted σ' hn₂ ((H.comap ⇑π.symm).comap ⇑j₂) hc₂⟧ : Flag σ' (Fin n₂)) = F₂)
          then unnormRootedDensity W hℓ (H.comap ⇑π.symm) u v else 0 :=
    Finset.sum_congr rfl (fun H _ => by
      rw [← unnormRootedDensity_comap_rootfix_perm W hℓ π.symm hπroots_symm H u v])
  rw [step2]
  exact Equiv.sum_comp (graphComapEquiv π.symm)
    (fun H' => if (∃ hc₁ : RootCompatible σ' hn₁ (H'.comap ⇑j₁),
        (⟦mkStdRooted σ' hn₁ (H'.comap ⇑j₁) hc₁⟧ : Flag σ' (Fin n₁)) = F₁)
      ∧ (∃ hc₂ : RootCompatible σ' hn₂ (H'.comap ⇑j₂),
        (⟦mkStdRooted σ' hn₂ (H'.comap ⇑j₂) hc₂⟧ : Flag σ' (Fin n₂)) = F₂)
      then unnormRootedDensity W hℓ H' u v else 0)

/-- **The key simplification**: for an `IsInducedPairOn` subset pair `P` realising two
standard-rooted flags of the exact sizes `n₁, n₂` glued into a host of size `n₁ + n₂ - 2`, the
second coordinate is forced to be the complement of the first, union the roots. -/
private lemma pair_snd_eq_compl_union_roots {n₁ n₂ ℓ : ℕ} (_hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    (hℓ : 2 ≤ ℓ) (hℓeq : ℓ = n₁ + n₂ - 2) (P : Finset (Fin ℓ) × Finset (Fin ℓ))
    (hsub1 : rootFinset hℓ ⊆ P.1) (hsub2 : rootFinset hℓ ⊆ P.2)
    (hdisj : ((↑P.1 : Set (Fin ℓ)) \ ↑(rootFinset hℓ)) ∩ ((↑P.2 : Set (Fin ℓ)) \ ↑(rootFinset hℓ))
      = ∅)
    (hcard1 : P.1.card = n₁) (hcard2 : P.2.card = n₂) : P.2 = P.1ᶜ ∪ rootFinset hℓ := by
  have hinter : P.1 ∩ P.2 = rootFinset hℓ := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_inter] at hx
      by_contra hxr
      have hx1 : x ∈ (↑P.1 : Set (Fin ℓ)) \ ↑(rootFinset hℓ) := ⟨hx.1, by simpa using hxr⟩
      have hx2 : x ∈ (↑P.2 : Set (Fin ℓ)) \ ↑(rootFinset hℓ) := ⟨hx.2, by simpa using hxr⟩
      rw [Set.eq_empty_iff_forall_notMem] at hdisj
      exact hdisj x ⟨hx1, hx2⟩
    · exact Finset.subset_inter hsub1 hsub2
  have hcardunion : (P.1 ∪ P.2).card = ℓ := by
    have hkey := Finset.card_union_add_card_inter P.1 P.2
    rw [hinter, rootFinset_card, hcard1, hcard2] at hkey
    omega
  have huniv : P.1 ∪ P.2 = Finset.univ := Finset.eq_univ_of_card _ (by rw [hcardunion, Fintype.card_fin])
  have hcompl_sub : P.1ᶜ ⊆ P.2 := by
    intro x hx
    have hxu : x ∈ P.1 ∪ P.2 := huniv ▸ Finset.mem_univ x
    rcases Finset.mem_union.mp hxu with h | h
    · exact absurd h (Finset.mem_compl.mp hx)
    · exact h
  have hsub_union : P.1ᶜ ∪ rootFinset hℓ ⊆ P.2 := Finset.union_subset hcompl_sub hsub2
  have hcard_union2 : (P.1ᶜ ∪ rootFinset hℓ).card = n₂ := by
    have hdisjcr : Disjoint P.1ᶜ (rootFinset hℓ) :=
      Finset.disjoint_left.mpr (fun x hx1 hx2 => (Finset.mem_compl.mp hx1) (hsub1 hx2))
    rw [Finset.card_union_of_disjoint hdisjcr, Finset.card_compl, hcard1, Fintype.card_fin,
      rootFinset_card]
    omega
  exact (Finset.eq_of_subset_of_card_le hsub_union (by rw [hcard2, hcard_union2])).symm

/-- `inducedLabeledSubgraph` depends only on the vertex set `S`, not on the proof that `S`
contains the roots (local copy of the private `PairSubsetCount.inducedLabeledSubgraph_congr'`,
inaccessible here since that lemma is private to its file). -/
private lemma inducedLabeledSubgraph_congr_set (σ' : FlagType (Fin 2)) {W' : Type}
    [Fintype W'] [DecidableEq W'] (G : LabeledGraph σ' W') {S₁ S₂ : Set W'} (hS : S₁ = S₂)
    (h₁ : G.type_verts ⊆ S₁) (h₂ : G.type_verts ⊆ S₂) :
    LabeledSubgraph.inducedLabeledSubgraph G S₁ h₁ = LabeledSubgraph.inducedLabeledSubgraph G S₂ h₂ := by
  subst hS; rfl

/-- **The card bijection between subset pairs and their first coordinate**: given the sizes
`n₁, n₂` are exactly right for the glued host `Fin (n₁ + n₂ - 2)`, every `IsInducedPairOn`
subset pair for a standard-rooted `H` has its second coordinate forced to be the complement of
the first (union the roots): the key simplification of the rooted `mulProp`. -/
private lemma card_pair_eq_card_subset1 (σ' : FlagType (Fin 2)) {n₁ n₂ : ℕ}
    (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂)
    {H : SimpleGraph (Fin (n₁ + n₂ - 2))} (hH : RootCompatible σ' (glue_le₂ hn₁ hn₂) H)
    {G₁ : SimpleGraph (Fin n₁)} (hG₁ : RootCompatible σ' hn₁ G₁)
    {G₂ : SimpleGraph (Fin n₂)} (hG₂ : RootCompatible σ' hn₂ G₂) :
    (Finset.univ.filter (fun P : Finset (Fin (n₁ + n₂ - 2)) × Finset (Fin (n₁ + n₂ - 2)) =>
        IsInducedPairOn (mkStdRooted σ' hn₁ G₁ hG₁) (mkStdRooted σ' hn₂ G₂ hG₂)
          (mkStdRooted σ' (glue_le₂ hn₁ hn₂) H hH) P)).card
      = (Finset.univ.filter (fun S₁ : Finset (Fin (n₁ + n₂ - 2)) =>
          rootFinset (glue_le₂ hn₁ hn₂) ⊆ S₁ ∧ S₁.card = n₁
          ∧ (∃ h₁ : (mkStdRooted σ' (glue_le₂ hn₁ hn₂) H hH).type_verts
                ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))),
              Nonempty ((LabeledSubgraph.inducedLabeledSubgraph
                  (mkStdRooted σ' (glue_le₂ hn₁ hn₂) H hH) (↑S₁) h₁).coe
                ≃f mkStdRooted σ' hn₁ G₁ hG₁))
          ∧ (∃ h₂ : (mkStdRooted σ' (glue_le₂ hn₁ hn₂) H hH).type_verts
                ⊆ (↑(S₁ᶜ ∪ rootFinset (glue_le₂ hn₁ hn₂)) : Set (Fin (n₁ + n₂ - 2))),
              Nonempty ((LabeledSubgraph.inducedLabeledSubgraph
                  (mkStdRooted σ' (glue_le₂ hn₁ hn₂) H hH)
                  (↑(S₁ᶜ ∪ rootFinset (glue_le₂ hn₁ hn₂))) h₂).coe
                ≃f mkStdRooted σ' hn₂ G₂ hG₂))
        )).card := by
  classical
  set hℓ := glue_le₂ hn₁ hn₂ with hℓdef
  have htv : (mkStdRooted σ' hℓ H hH).type_verts = (↑(rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))) := by
    rw [mkStdRooted_type_verts, rootFinset_coe]
  refine Finset.card_bij' (fun P _ => P.1) (fun S₁ _ => (S₁, S₁ᶜ ∪ rootFinset hℓ)) ?hi ?hj ?hleft ?hright
  case hi =>
    intro P hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
    unfold IsInducedPairOn at hP
    obtain ⟨hdisj, ⟨h1, e1⟩, ⟨h2, e2⟩⟩ := hP
    have hcard1 : P.1.card = n₁ := card_eq_of_stdRooted_subset_iso σ' hn₁ hℓ hH hG₁ h1 (Classical.choice e1)
    have hcard2 : P.2.card = n₂ := card_eq_of_stdRooted_subset_iso σ' hn₂ hℓ hH hG₂ h2 (Classical.choice e2)
    have hsub1 : rootFinset hℓ ⊆ P.1 := Finset.coe_subset.mp (htv ▸ h1)
    have hsub2 : rootFinset hℓ ⊆ P.2 := Finset.coe_subset.mp (htv ▸ h2)
    have hdisj' : ((↑P.1 : Set (Fin (n₁ + n₂ - 2))) \ ↑(rootFinset hℓ))
        ∩ ((↑P.2 : Set (Fin (n₁ + n₂ - 2))) \ ↑(rootFinset hℓ)) = ∅ := htv ▸ hdisj
    have hP2eq : P.2 = P.1ᶜ ∪ rootFinset hℓ :=
      pair_snd_eq_compl_union_roots hn₁ hn₂ hℓ rfl P hsub1 hsub2 hdisj' hcard1 hcard2
    have hSeq : (↑P.2 : Set (Fin (n₁ + n₂ - 2))) = ↑(P.1ᶜ ∪ rootFinset hℓ) := by rw [hP2eq]
    have h2new : (mkStdRooted σ' hℓ H hH).type_verts
        ⊆ (↑(P.1ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))) := hSeq ▸ h2
    have heq2 := inducedLabeledSubgraph_congr_set σ' (mkStdRooted σ' hℓ H hH) hSeq h2 h2new
    have e2new : Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hH)
        (↑(P.1ᶜ ∪ rootFinset hℓ)) h2new).coe ≃f mkStdRooted σ' hn₂ G₂ hG₂) := heq2 ▸ e2
    exact ⟨hsub1, hcard1, ⟨h1, e1⟩, ⟨h2new, e2new⟩⟩
  case hj =>
    intro S₁ hS₁
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS₁ ⊢
    obtain ⟨-, hcard1, ⟨h1, e1⟩, ⟨h2, e2⟩⟩ := hS₁
    unfold IsInducedPairOn
    have hdisjgen : ((↑S₁ : Set (Fin (n₁ + n₂ - 2))) \ (mkStdRooted σ' hℓ H hH).type_verts)
        ∩ ((↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))) \ (mkStdRooted σ' hℓ H hH).type_verts)
        = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨⟨hxS1, hxnv1⟩, ⟨hxS2, -⟩⟩
      rw [Finset.coe_union, Set.mem_union] at hxS2
      rcases hxS2 with hxS2 | hxS2
      · exact (Finset.mem_compl.mp (Finset.mem_coe.mp hxS2)) (Finset.mem_coe.mp hxS1)
      · exact hxnv1 (by rw [htv]; exact hxS2)
    exact ⟨hdisjgen, ⟨h1, e1⟩, ⟨h2, e2⟩⟩
  case hleft =>
    intro P hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
    unfold IsInducedPairOn at hP
    obtain ⟨hdisj, ⟨h1, e1⟩, ⟨h2, e2⟩⟩ := hP
    have hcard1 : P.1.card = n₁ := card_eq_of_stdRooted_subset_iso σ' hn₁ hℓ hH hG₁ h1 (Classical.choice e1)
    have hcard2 : P.2.card = n₂ := card_eq_of_stdRooted_subset_iso σ' hn₂ hℓ hH hG₂ h2 (Classical.choice e2)
    have hsub1 : rootFinset hℓ ⊆ P.1 := Finset.coe_subset.mp (htv ▸ h1)
    have hsub2 : rootFinset hℓ ⊆ P.2 := Finset.coe_subset.mp (htv ▸ h2)
    have hdisj' : ((↑P.1 : Set (Fin (n₁ + n₂ - 2))) \ ↑(rootFinset hℓ))
        ∩ ((↑P.2 : Set (Fin (n₁ + n₂ - 2))) \ ↑(rootFinset hℓ)) = ∅ := htv ▸ hdisj
    have hP2eq : P.2 = P.1ᶜ ∪ rootFinset hℓ :=
      pair_snd_eq_compl_union_roots hn₁ hn₂ hℓ rfl P hsub1 hsub2 hdisj' hcard1 hcard2
    exact Prod.ext rfl hP2eq.symm
  case hright =>
    intro S₁ _
    rfl

/-- **The rooted block-product chain-rule core**: the pair analogue of
`graphonRootedProfile_zeroSpace_aux`. -/
private lemma graphonRootedProfile_mul_aux (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (F₁ : Flag σ' (Fin n₁)) (F₂ : Flag σ' (Fin n₂)) :
    (∑ H : SimpleGraph (Fin (n₁ + n₂ - 2)), if (∃ hc₁ : RootCompatible σ' hn₁
          (H.comap ⇑(Fin.castLEEmb (glue_le₁ hn₁ hn₂))),
        (⟦mkStdRooted σ' hn₁ (H.comap ⇑(Fin.castLEEmb (glue_le₁ hn₁ hn₂))) hc₁⟧
          : Flag σ' (Fin n₁)) = F₁)
      ∧ (∃ hc₂ : RootCompatible σ' hn₂ (H.comap ⇑(glueEmb₂ n₁ hn₁ hn₂)),
        (⟦mkStdRooted σ' hn₂ (H.comap ⇑(glueEmb₂ n₁ hn₁ hn₂)) hc₂⟧ : Flag σ' (Fin n₂)) = F₂)
      then unnormRootedDensity W (glue_le₂ hn₁ hn₂) H u v else 0)
      = ∑ Gℓ : FlagWithSize σ' (n₁ + n₂ - 2), (flagDensity₂ F₁ F₂ Gℓ : ℝ) *
          (∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) =>
              ∃ h : RootCompatible σ' (glue_le₂ hn₁ hn₂) H,
                (⟦mkStdRooted σ' (glue_le₂ hn₁ hn₂) H h⟧ : Flag σ' (Fin (n₁ + n₂ - 2))) = Gℓ),
              unnormRootedDensity W (glue_le₂ hn₁ hn₂) H u v) := by
  set hℓ := glue_le₂ hn₁ hn₂ with hℓdef
  set glue1 : Fin n₁ ↪ Fin (n₁ + n₂ - 2) := Fin.castLEEmb (glue_le₁ hn₁ hn₂) with hglue1def
  set glue2 : Fin n₂ ↪ Fin (n₁ + n₂ - 2) := glueEmb₂ n₁ hn₁ hn₂ with hglue2def
  have hglue1 : RootFixing hn₁ hℓ glue1 := rootFixing_castLE hn₁ hℓ (glue_le₁ hn₁ hn₂)
  have hglue2 : RootFixing hn₂ hℓ glue2 := rootFixing_glueEmb₂ hn₁ hn₂
  have hglueInter : Set.range ⇑glue1 ∩ Set.range ⇑glue2
      = ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin (n₁ + n₂ - 2))) := glue_range_inter hn₁ hn₂
  obtain ⟨Grep1, hGrep1, hGrep1Eq⟩ := exists_stdRooted_rep hn₁ F₁
  obtain ⟨Grep2, hGrep2, hGrep2Eq⟩ := exists_stdRooted_rep hn₂ F₂
  set sVal : ℝ := ∑ H : SimpleGraph (Fin (n₁ + n₂ - 2)),
      if (∃ hc1 : RootCompatible σ' hn₁ (H.comap ⇑glue1),
          (⟦mkStdRooted σ' hn₁ (H.comap ⇑glue1) hc1⟧ : Flag σ' (Fin n₁)) = F₁)
        ∧ (∃ hc2 : RootCompatible σ' hn₂ (H.comap ⇑glue2),
          (⟦mkStdRooted σ' hn₂ (H.comap ⇑glue2) hc2⟧ : Flag σ' (Fin n₂)) = F₂)
      then unnormRootedDensity W hℓ H u v else 0 with hsValdef
  show sVal = _
  have hchoose_pos : 0 < (n₁ + n₂ - 2 - 2).choose (n₁ - 2) := Nat.choose_pos (by omega)
  have hchoose_ne : ((n₁ + n₂ - 2 - 2).choose (n₁ - 2) : ℝ) ≠ 0 := by exact_mod_cast hchoose_pos.ne'
  have hT_S1 : ∀ S₁ : Finset (Fin (n₁ + n₂ - 2)),
      (∑ H : SimpleGraph (Fin (n₁ + n₂ - 2)), if (∃ hHp : RootCompatible σ' hℓ H,
            ∃ h1 : (mkStdRooted σ' hℓ H hHp).type_verts ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))),
              Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp) (↑S₁) h1).coe
                ≃f mkStdRooted σ' hn₁ Grep1 hGrep1))
          ∧ (∃ hHp' : RootCompatible σ' hℓ H,
            ∃ h2 : (mkStdRooted σ' hℓ H hHp').type_verts
                ⊆ (↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))),
              Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp')
                  (↑(S₁ᶜ ∪ rootFinset hℓ)) h2).coe ≃f mkStdRooted σ' hn₂ Grep2 hGrep2))
          then unnormRootedDensity W hℓ H u v else 0)
        = if (rootFinset hℓ ⊆ S₁ ∧ S₁.card = n₁) then sVal else 0 := by
    intro S₁
    by_cases hcond : rootFinset hℓ ⊆ S₁ ∧ S₁.card = n₁
    · rw [if_pos hcond]
      obtain ⟨hrootsub, hcard⟩ := hcond
      have hrootsub' : ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin (n₁ + n₂ - 2)))
          ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))) := by
        rw [← rootFinset_coe hℓ]; exact_mod_cast hrootsub
      obtain ⟨j₁, hj₁, hS₁range⟩ := exists_rootFixing_emb_range hn₁ hℓ S₁ hrootsub' hcard
      have hdisjS1 : Disjoint S₁ᶜ (rootFinset hℓ) :=
        Finset.disjoint_left.mpr (fun x hx1 hx2 => (Finset.mem_compl.mp hx1) (hrootsub hx2))
      have hS₂card : (S₁ᶜ ∪ rootFinset hℓ).card = n₂ := by
        rw [Finset.card_union_of_disjoint hdisjS1, Finset.card_compl, hcard, Fintype.card_fin,
          rootFinset_card]
        omega
      have hS₂rootsub : ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin (n₁ + n₂ - 2)))
          ⊆ (↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))) := by
        rw [← rootFinset_coe hℓ]
        exact_mod_cast Finset.subset_union_right
      obtain ⟨j₂, hj₂, hS₂range⟩ :=
        exists_rootFixing_emb_range hn₂ hℓ (S₁ᶜ ∪ rootFinset hℓ) hS₂rootsub hS₂card
      have hjInter : Set.range ⇑j₁ ∩ Set.range ⇑j₂
          = ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin (n₁ + n₂ - 2))) := by
        rw [hS₁range, hS₂range, Finset.coe_union, Finset.coe_compl,
          Set.inter_union_distrib_left, Set.inter_compl_self, Set.empty_union,
          Set.inter_eq_right.mpr (Finset.coe_subset.mpr hrootsub)]
        exact rootFinset_coe hℓ
      have hconv : (∑ H : SimpleGraph (Fin (n₁ + n₂ - 2)), if (∃ hHp : RootCompatible σ' hℓ H,
              ∃ h1 : (mkStdRooted σ' hℓ H hHp).type_verts ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp) (↑S₁) h1).coe
                  ≃f mkStdRooted σ' hn₁ Grep1 hGrep1))
            ∧ (∃ hHp' : RootCompatible σ' hℓ H,
              ∃ h2 : (mkStdRooted σ' hℓ H hHp').type_verts
                  ⊆ (↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp')
                    (↑(S₁ᶜ ∪ rootFinset hℓ)) h2).coe ≃f mkStdRooted σ' hn₂ Grep2 hGrep2))
            then unnormRootedDensity W hℓ H u v else 0)
          = ∑ H : SimpleGraph (Fin (n₁ + n₂ - 2)), if (∃ hc1 : RootCompatible σ' hn₁ (H.comap ⇑j₁),
              (⟦mkStdRooted σ' hn₁ (H.comap ⇑j₁) hc1⟧ : Flag σ' (Fin n₁)) = F₁)
            ∧ (∃ hc2 : RootCompatible σ' hn₂ (H.comap ⇑j₂),
              (⟦mkStdRooted σ' hn₂ (H.comap ⇑j₂) hc2⟧ : Flag σ' (Fin n₂)) = F₂)
            then unnormRootedDensity W hℓ H u v else 0 := by
        apply Finset.sum_congr rfl
        intro H _
        congr 1
        rw [eq_iff_iff]
        constructor
        · rintro ⟨⟨hHp, h1, e1⟩, ⟨hHp', h2, e2⟩⟩
          refine ⟨⟨rootCompatible_comap_of_rootFixing hn₁ hℓ j₁ hj₁ hHp, ?_⟩,
            ⟨rootCompatible_comap_of_rootFixing hn₂ hℓ j₂ hj₂ hHp', ?_⟩⟩
          · rw [← hGrep1Eq]
            exact (stdRooted_subset_iso_iff hn₁ hℓ H hHp Grep1 hGrep1 j₁ hj₁ S₁ hS₁range).mp ⟨h1, e1⟩
          · rw [← hGrep2Eq]
            exact (stdRooted_subset_iso_iff hn₂ hℓ H hHp' Grep2 hGrep2 j₂ hj₂
              (S₁ᶜ ∪ rootFinset hℓ) hS₂range).mp ⟨h2, e2⟩
        · rintro ⟨⟨hc1, e1⟩, ⟨hc2, e2⟩⟩
          have hHp : RootCompatible σ' hℓ H :=
            (rootCompatible_comap_rootFixing_iff σ' hn₁ hℓ j₁ hj₁ H).mp hc1
          have hHp' : RootCompatible σ' hℓ H :=
            (rootCompatible_comap_rootFixing_iff σ' hn₂ hℓ j₂ hj₂ H).mp hc2
          refine ⟨⟨hHp, ?_⟩, ⟨hHp', ?_⟩⟩
          · apply (stdRooted_subset_iso_iff hn₁ hℓ H hHp Grep1 hGrep1 j₁ hj₁ S₁ hS₁range).mpr
            rw [hGrep1Eq]; exact e1
          · apply (stdRooted_subset_iso_iff hn₂ hℓ H hHp' Grep2 hGrep2 j₂ hj₂
              (S₁ᶜ ∪ rootFinset hℓ) hS₂range).mpr
            rw [hGrep2Eq]; exact e2
      rw [hconv, hsValdef]
      exact sum_unnormRootedDensity_comap_rootfix_pair_embedding_eq W σ' u v hn₁ hn₂ hℓ F₁ F₂
        glue1 j₁ glue2 j₂ hglue1 hj₁ hglue2 hj₂ hglueInter hjInter
    · rw [if_neg hcond]
      apply Finset.sum_eq_zero
      intro H _
      apply if_neg
      rintro ⟨⟨hHp, h1, e1⟩, ⟨hHp', h2, e2⟩⟩
      apply hcond
      have hc1 : S₁.card = n₁ :=
        card_eq_of_stdRooted_subset_iso σ' hn₁ hℓ hHp hGrep1 h1 (Classical.choice e1)
      have hrsub : rootFinset hℓ ⊆ S₁ := by
        rw [← Finset.coe_subset, rootFinset_coe, ← mkStdRooted_type_verts hℓ H hHp]
        exact h1
      exact ⟨hrsub, hc1⟩
  have hT1 : (∑ S₁ : Finset (Fin (n₁ + n₂ - 2)), ∑ H : SimpleGraph (Fin (n₁ + n₂ - 2)),
        (if (∃ hHp : RootCompatible σ' hℓ H,
              ∃ h1 : (mkStdRooted σ' hℓ H hHp).type_verts ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp) (↑S₁) h1).coe
                  ≃f mkStdRooted σ' hn₁ Grep1 hGrep1))
            ∧ (∃ hHp' : RootCompatible σ' hℓ H,
              ∃ h2 : (mkStdRooted σ' hℓ H hHp').type_verts
                  ⊆ (↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp')
                    (↑(S₁ᶜ ∪ rootFinset hℓ)) h2).coe ≃f mkStdRooted σ' hn₂ Grep2 hGrep2))
            then unnormRootedDensity W hℓ H u v else 0))
      = ((n₁ + n₂ - 2 - 2).choose (n₁ - 2) : ℝ) * sVal := by
    rw [Finset.sum_congr rfl (fun S₁ _ => hT_S1 S₁), sum_ite_const_rooted]
    congr 1
    have hfeq : (Finset.univ.filter (fun S₁ : Finset (Fin (n₁ + n₂ - 2)) =>
          rootFinset hℓ ⊆ S₁ ∧ S₁.card = n₁))
        = (Finset.univ.filter (fun S₁ : Finset (Fin (n₁ + n₂ - 2)) =>
            ({Fin.castLE hℓ 0, Fin.castLE hℓ 1} : Set (Fin (n₁ + n₂ - 2))) ⊆ ↑S₁
              ∧ S₁.card = n₁)) := by
      apply Finset.filter_congr
      intro S₁ _
      rw [← rootFinset_coe hℓ, Finset.coe_subset]
    rw [hfeq]
    exact_mod_cast count_rootContaining_subsets hn₁ hℓ (glue_le₁ hn₁ hn₂)
  have hT2 : (∑ S₁ : Finset (Fin (n₁ + n₂ - 2)), ∑ H : SimpleGraph (Fin (n₁ + n₂ - 2)),
        (if (∃ hHp : RootCompatible σ' hℓ H,
              ∃ h1 : (mkStdRooted σ' hℓ H hHp).type_verts ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp) (↑S₁) h1).coe
                  ≃f mkStdRooted σ' hn₁ Grep1 hGrep1))
            ∧ (∃ hHp' : RootCompatible σ' hℓ H,
              ∃ h2 : (mkStdRooted σ' hℓ H hHp').type_verts
                  ⊆ (↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp')
                    (↑(S₁ᶜ ∪ rootFinset hℓ)) h2).coe ≃f mkStdRooted σ' hn₂ Grep2 hGrep2))
            then unnormRootedDensity W hℓ H u v else 0))
      = ((n₁ + n₂ - 2 - 2).choose (n₁ - 2) : ℝ) *
        ∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) =>
            RootCompatible σ' hℓ H),
          (flagDensity₂ F₁ F₂ (rootedClassOf σ' hℓ H) : ℝ) * unnormRootedDensity W hℓ H u v := by
    rw [Finset.sum_comm]
    have hstep : (∑ H : SimpleGraph (Fin (n₁ + n₂ - 2)), ∑ S₁ : Finset (Fin (n₁ + n₂ - 2)),
          (if (∃ hHp : RootCompatible σ' hℓ H,
                ∃ h1 : (mkStdRooted σ' hℓ H hHp).type_verts ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))),
                  Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp) (↑S₁) h1).coe
                    ≃f mkStdRooted σ' hn₁ Grep1 hGrep1))
              ∧ (∃ hHp' : RootCompatible σ' hℓ H,
                ∃ h2 : (mkStdRooted σ' hℓ H hHp').type_verts
                    ⊆ (↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))),
                  Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp')
                      (↑(S₁ᶜ ∪ rootFinset hℓ)) h2).coe ≃f mkStdRooted σ' hn₂ Grep2 hGrep2))
              then unnormRootedDensity W hℓ H u v else 0))
        = ∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) =>
              RootCompatible σ' hℓ H),
            ∑ S₁ : Finset (Fin (n₁ + n₂ - 2)),
            (if (∃ hHp : RootCompatible σ' hℓ H,
                  ∃ h1 : (mkStdRooted σ' hℓ H hHp).type_verts ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))),
                    Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp)
                        (↑S₁) h1).coe ≃f mkStdRooted σ' hn₁ Grep1 hGrep1))
                ∧ (∃ hHp' : RootCompatible σ' hℓ H,
                  ∃ h2 : (mkStdRooted σ' hℓ H hHp').type_verts
                      ⊆ (↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))),
                    Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp')
                        (↑(S₁ᶜ ∪ rootFinset hℓ)) h2).coe ≃f mkStdRooted σ' hn₂ Grep2 hGrep2))
                then unnormRootedDensity W hℓ H u v else 0) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro H _ hHnotin
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hHnotin
      apply Finset.sum_eq_zero
      intro S₁ _
      apply if_neg
      rintro ⟨⟨hHp, -, -⟩, -⟩
      exact hHnotin hHp
    rw [hstep, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H hHmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hHmem
    rw [sum_ite_const_rooted]
    have hSetEq : (Finset.univ.filter (fun S₁ : Finset (Fin (n₁ + n₂ - 2)) =>
          (∃ hHp : RootCompatible σ' hℓ H,
              ∃ h1 : (mkStdRooted σ' hℓ H hHp).type_verts ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp) (↑S₁) h1).coe
                  ≃f mkStdRooted σ' hn₁ Grep1 hGrep1))
          ∧ (∃ hHp' : RootCompatible σ' hℓ H,
              ∃ h2 : (mkStdRooted σ' hℓ H hHp').type_verts
                  ⊆ (↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp')
                    (↑(S₁ᶜ ∪ rootFinset hℓ)) h2).coe ≃f mkStdRooted σ' hn₂ Grep2 hGrep2))))
        = (Finset.univ.filter (fun S₁ : Finset (Fin (n₁ + n₂ - 2)) =>
            rootFinset hℓ ⊆ S₁ ∧ S₁.card = n₁
            ∧ (∃ h1 : (mkStdRooted σ' hℓ H hHmem).type_verts ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHmem) (↑S₁) h1).coe
                  ≃f mkStdRooted σ' hn₁ Grep1 hGrep1))
            ∧ (∃ h2 : (mkStdRooted σ' hℓ H hHmem).type_verts
                  ⊆ (↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHmem)
                    (↑(S₁ᶜ ∪ rootFinset hℓ)) h2).coe ≃f mkStdRooted σ' hn₂ Grep2 hGrep2)))) := by
      apply Finset.filter_congr
      intro S₁ _
      constructor
      · rintro ⟨⟨hHp, h1, e1⟩, ⟨hHp', h2, e2⟩⟩
        have hc1 : S₁.card = n₁ :=
          card_eq_of_stdRooted_subset_iso σ' hn₁ hℓ hHp hGrep1 h1 (Classical.choice e1)
        have hrsub : rootFinset hℓ ⊆ S₁ := by
          rw [← Finset.coe_subset, rootFinset_coe, ← mkStdRooted_type_verts hℓ H hHp]
          exact h1
        exact ⟨hrsub, hc1, ⟨h1, e1⟩, ⟨h2, e2⟩⟩
      · rintro ⟨-, -, ⟨h1, e1⟩, ⟨h2, e2⟩⟩
        exact ⟨⟨hHmem, h1, e1⟩, ⟨hHmem, h2, e2⟩⟩
    have hcount_eq_card : (Finset.univ.filter (fun S₁ : Finset (Fin (n₁ + n₂ - 2)) =>
          (∃ hHp : RootCompatible σ' hℓ H,
              ∃ h1 : (mkStdRooted σ' hℓ H hHp).type_verts ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp) (↑S₁) h1).coe
                  ≃f mkStdRooted σ' hn₁ Grep1 hGrep1))
          ∧ (∃ hHp' : RootCompatible σ' hℓ H,
              ∃ h2 : (mkStdRooted σ' hℓ H hHp').type_verts
                  ⊆ (↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp')
                    (↑(S₁ᶜ ∪ rootFinset hℓ)) h2).coe ≃f mkStdRooted σ' hn₂ Grep2 hGrep2)))).card
        = (Finset.univ.filter (fun P : Finset (Fin (n₁ + n₂ - 2)) × Finset (Fin (n₁ + n₂ - 2)) =>
            IsInducedPairOn (mkStdRooted σ' hn₁ Grep1 hGrep1) (mkStdRooted σ' hn₂ Grep2 hGrep2)
              (mkStdRooted σ' hℓ H hHmem) P)).card := by
      rw [hSetEq]; exact (card_pair_eq_card_subset1 σ' hn₁ hn₂ hHmem hGrep1 hGrep2).symm
    have hfd := flagDensity₂_stdRooted σ' hn₁ hn₂ hℓ Grep1 hGrep1 Grep2 hGrep2 H hHmem
    have hab : (n₁ - 2) + (n₂ - 2) = n₁ + n₂ - 2 - 2 := by omega
    have hmulti : multinomialCoefficient ![n₁ - 2, n₂ - 2] (n₁ + n₂ - 2 - 2)
        = (n₁ + n₂ - 2 - 2).choose (n₁ - 2) := by
      rw [← hab]; exact multinomialCoefficient_two_eq_choose (n₁ - 2) (n₂ - 2)
    rw [hmulti] at hfd
    have hDne : ((n₁ + n₂ - 2 - 2).choose (n₁ - 2) : ℚ) ≠ 0 := by
      exact_mod_cast hchoose_pos.ne'
    have hcountQ : ((Finset.univ.filter (fun P : Finset (Fin (n₁ + n₂ - 2)) × Finset (Fin (n₁ + n₂ - 2)) =>
            IsInducedPairOn (mkStdRooted σ' hn₁ Grep1 hGrep1) (mkStdRooted σ' hn₂ Grep2 hGrep2)
              (mkStdRooted σ' hℓ H hHmem) P)).card : ℚ)
        = flagDensity₂ (⟦mkStdRooted σ' hn₁ Grep1 hGrep1⟧ : Flag σ' (Fin n₁))
            (⟦mkStdRooted σ' hn₂ Grep2 hGrep2⟧ : Flag σ' (Fin n₂))
            (⟦mkStdRooted σ' hℓ H hHmem⟧ : Flag σ' (Fin (n₁ + n₂ - 2)))
          * ((n₁ + n₂ - 2 - 2).choose (n₁ - 2) : ℚ) := ((eq_div_iff hDne).mp hfd).symm
    rw [hGrep1Eq, hGrep2Eq, ← rootedClassOf_eq_of_rootCompatible σ' hℓ hHmem] at hcountQ
    have hcountR : ((Finset.univ.filter (fun S₁ : Finset (Fin (n₁ + n₂ - 2)) =>
          (∃ hHp : RootCompatible σ' hℓ H,
              ∃ h1 : (mkStdRooted σ' hℓ H hHp).type_verts ⊆ (↑S₁ : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp) (↑S₁) h1).coe
                  ≃f mkStdRooted σ' hn₁ Grep1 hGrep1))
          ∧ (∃ hHp' : RootCompatible σ' hℓ H,
              ∃ h2 : (mkStdRooted σ' hℓ H hHp').type_verts
                  ⊆ (↑(S₁ᶜ ∪ rootFinset hℓ) : Set (Fin (n₁ + n₂ - 2))),
                Nonempty ((LabeledSubgraph.inducedLabeledSubgraph (mkStdRooted σ' hℓ H hHp')
                    (↑(S₁ᶜ ∪ rootFinset hℓ)) h2).coe ≃f mkStdRooted σ' hn₂ Grep2 hGrep2)))).card : ℝ)
        = (flagDensity₂ F₁ F₂ (rootedClassOf σ' hℓ H) : ℝ)
          * ((n₁ + n₂ - 2 - 2).choose (n₁ - 2) : ℝ) := by
      rw [hcount_eq_card]; exact_mod_cast hcountQ
    rw [hcountR]; ring
  have hsVal_eq : sVal = ∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) =>
        RootCompatible σ' hℓ H),
      (flagDensity₂ F₁ F₂ (rootedClassOf σ' hℓ H) : ℝ) * unnormRootedDensity W hℓ H u v :=
    mul_left_cancel₀ hchoose_ne (hT1.symm.trans hT2)
  rw [hsVal_eq]
  rw [← Finset.sum_fiberwise
      (Finset.univ.filter (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) => RootCompatible σ' hℓ H))
      (rootedClassOf σ' hℓ)
      (fun H => (flagDensity₂ F₁ F₂ (rootedClassOf σ' hℓ H) : ℝ) * unnormRootedDensity W hℓ H u v)]
  apply Finset.sum_congr rfl
  intro Gℓ _
  have hrw : ∀ H ∈ (Finset.univ.filter (fun H : SimpleGraph (Fin (n₁ + n₂ - 2)) =>
        RootCompatible σ' hℓ H)).filter (fun H => rootedClassOf σ' hℓ H = Gℓ),
      (flagDensity₂ F₁ F₂ (rootedClassOf σ' hℓ H) : ℝ) * unnormRootedDensity W hℓ H u v
        = (flagDensity₂ F₁ F₂ Gℓ : ℝ) * unnormRootedDensity W hℓ H u v := by
    intro H hH
    rw [(Finset.mem_filter.mp hH).2]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr
  · ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hH, hcl⟩
      exact ⟨hH, by rw [← rootedClassOf_eq_of_rootCompatible σ' hℓ hH]; exact hcl⟩
    · rintro ⟨hH, hcl⟩
      exact ⟨hH, by rw [rootedClassOf_eq_of_rootCompatible σ' hℓ hH]; exact hcl⟩
  · intro H _; rfl

theorem graphonRootedProfile_mulProp (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    (_h : RootAdmissible W σ' u v) : mulProp (graphonRootedProfileFun W σ' u v) := by
  -- Multiplicativity, via the glued block product + pair averaging scheme.
  -- Sizes: `F₁.1 + F₂.1 − n₀` with `n₀ = 2` is the glued host size of
  -- `unnormRootedDensity_block_mul`; the conditioning bookkeeping (`rootWeight⁻²` on the
  -- left, one `rootWeight` in the glued sum) cancels against the single `rootWeight⁻¹` of
  -- each right-hand profile value.  Pair count from `flagDensity₂_eq_subset_count_div`
  -- (general σ, `PairSubsetCount`), pair averaging from
  -- `exists_rootfix_perm_comp_emb_pair` with `glue_range_inter` supplying the overlap
  -- hypothesis for the glue embeddings, and the multinomial denominator
  -- `multinomialCoefficient ![n₁−2, n₂−2] (n₁+n₂−4)` reduced via
  -- `multinomialCoefficient_eq_choose_mul_multinomial`.
  intro F₁ F₂
  show graphonRootedProfileFun W σ' u v F₁ * graphonRootedProfileFun W σ' u v F₂
      = ∑ G : FlagWithSize σ' (F₁.1 + F₂.1 - 2), (flagDensity₂ F₁.2 F₂.2 G : ℝ) *
          graphonRootedProfileFun W σ' u v ⟨F₁.1 + F₂.1 - 2, G⟩
  have hn₁ : 2 ≤ F₁.1 := finFlag_size_ge_n₀ F₁
  have hn₂ : 2 ≤ F₂.1 := finFlag_size_ge_n₀ F₂
  unfold graphonRootedProfileFun
  have hmain : (∑ G₁ ∈ Finset.univ.filter (fun G₁ : SimpleGraph (Fin F₁.1) =>
        ∃ h : RootCompatible σ' hn₁ G₁, (⟦mkStdRooted σ' hn₁ G₁ h⟧ : Flag σ' (Fin F₁.1)) = F₁.2),
        unnormRootedDensity W hn₁ G₁ u v)
      * (∑ G₂ ∈ Finset.univ.filter (fun G₂ : SimpleGraph (Fin F₂.1) =>
        ∃ h : RootCompatible σ' hn₂ G₂, (⟦mkStdRooted σ' hn₂ G₂ h⟧ : Flag σ' (Fin F₂.1)) = F₂.2),
        unnormRootedDensity W hn₂ G₂ u v)
      = rootWeight W σ' u v * ∑ G : FlagWithSize σ' (F₁.1 + F₂.1 - 2),
          (flagDensity₂ F₁.2 F₂.2 G : ℝ) *
          (∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin (F₁.1 + F₂.1 - 2)) =>
              ∃ h : RootCompatible σ' (glue_le₂ hn₁ hn₂) H,
                (⟦mkStdRooted σ' (glue_le₂ hn₁ hn₂) H h⟧
                  : Flag σ' (Fin (F₁.1 + F₂.1 - 2))) = G),
              unnormRootedDensity W (glue_le₂ hn₁ hn₂) H u v) := by
    rw [Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl (fun G₁ hG₁mem => Finset.sum_congr rfl (fun G₂ hG₂mem => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG₁mem hG₂mem
      obtain ⟨hc₁, -⟩ := hG₁mem
      obtain ⟨hc₂, -⟩ := hG₂mem
      exact unnormRootedDensity_block_mul W σ' hn₁ hn₂ G₁ G₂ hc₁ hc₂ u v))]
    simp_rw [← Finset.mul_sum]
    congr 1
    rw [sum_double_fiberwise, Finset.sum_filter, ← graphonRootedProfile_mul_aux W σ' u v hn₁ hn₂ F₁.2 F₂.2]
    apply Finset.sum_congr rfl
    intro H _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rcases eq_or_ne (rootWeight W σ' u v) 0 with hw0 | hw0
  · simp [hw0]
  · rw [div_mul_div_comm, hmain, mul_div_mul_left _ _ hw0, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro G _
    rw [mul_div_assoc]

/-! ## The homomorphism -/

/-- The rooted profile packaged in the density-profile space (requires admissibility for the
`[0,1]` bounds' sharp side; the values are `[0,1]` for every pair by the junk-division
convention). -/
noncomputable def graphonRootedProfile (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I) :
    FlagDensitySpace σ' :=
  ⟨graphonRootedProfileFun W σ' u v, by
    simp only [FlagDensitySpace, Set.pi_univ_Icc, Set.mem_Icc]
    exact ⟨fun F => graphonRootedProfileFun_nonneg W σ' u v F,
           fun F => graphonRootedProfileFun_le_one W σ' u v F⟩⟩

@[simp]
theorem graphonRootedProfile_apply (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    (F : FinFlag σ') :
    (graphonRootedProfile W σ' u v : FinFlag σ' → ℝ) F
      = graphonRootedProfileFun W σ' u v F := rfl

/-- **The rooted conditional homomorphism** of the graphon `W` at the two-vertex type `σ'`
and the admissible pinned pair `(u, v)`: the view of `φ_W` from a `W`-random root pair. -/
noncomputable def graphonRootedHom (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    (h : RootAdmissible W σ' u v) : PositiveHom σ' :=
  positiveHomFromZeroSpaceOneMulProp (graphonRootedProfile W σ' u v)
    (graphonRootedProfile_zeroSpaceProp W σ' u v h)
    (graphonRootedProfile_oneProp W σ' u v h)
    (graphonRootedProfile_mulProp W σ' u v h)

@[simp]
theorem graphonRootedHom_coe (W : Graphon) (σ' : FlagType (Fin 2)) (u v : I)
    (h : RootAdmissible W σ' u v) (F : FinFlag σ') :
    (graphonRootedHom W σ' u v h).coe F = graphonRootedProfileFun W σ' u v F := by
  show linearExtension (graphonRootedProfile W σ' u v) (basisVector F)
      = (graphonRootedProfile W σ' u v : FinFlag σ' → ℝ) F
  rw [linearExtension_basisVector]

end FlagAlgebras.MetaTheory
