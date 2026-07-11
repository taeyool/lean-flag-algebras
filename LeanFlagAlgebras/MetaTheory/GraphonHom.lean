import LeanFlagAlgebras.MetaTheory.GraphonInducedDensity
import LeanFlagAlgebras.MetaTheory.EmptyTypeGraphBridge
import LeanFlagAlgebras.MetaTheory.C4Free

/-! # Every graphon is a positive homomorphism: `φ_W`

Infrastructure toward the representation results of §11.7 of `MetaTheory/paper.tex`, which use
"graphons are limit objects" as a folklore input; there is no single paper display for this
construction. For a graphon `W` we build the positive homomorphism `φ_W : A^{∅ₜ} → ℝ` whose
value on an unlabelled flag `F` is the probability that a `W`-random graph on `|F|` uniformly
sampled points is isomorphic to `F`:

`graphonProfileFun W F = ∑_{H : SimpleGraph (Fin |F|), ⟦H⟧ = F} graphonFlagDensity W H`.

The three structural properties of a density profile are discharged as follows and the
homomorphism is assembled by `positiveHomFromZeroSpaceOneMulProp`, following the same scheme
as `MetaTheory/ComplementHom.lean` but proved here from scratch for the graphon profile:

* `oneProp` — on `Fin 0` there is one graph, of density `1` (`graphonFlagDensity_fin_zero`).
* `zeroSpaceProp` — the chain rule.  Expand each labelled density through the extension
  partition (`graphonFlagDensity_extension_sum`), then average over the `C(ℓ,n)` vertex
  subsets: each subset is reached from the initial segment by a permutation
  (`exists_perm_comp_emb` + `graphonFlagDensity_comap_equiv` + `graphFlag_comap_equiv`), and
  the resulting subset count is exactly `flagDensity₁` (`flagDensity₁_graphFlag`); regroup the
  labelled sum by flag class (`Finset.sum_fiberwise`).
* `mulProp` — the same scheme run on the block product
  (`graphonFlagDensity_block_mul`), averaging over ordered disjoint subset pairs
  (`exists_perm_comp_emb_pair`), with the pair count given by `flagDensity₂_graphFlag`.

Main definitions and results:

* `graphonProfile W : FlagDensitySpace ∅ₜ` — the profile, with the three properties
  `graphonProfile_zeroSpaceProp` / `graphonProfile_oneProp` / `graphonProfile_mulProp`;
* `graphonHom W : PositiveHom ∅ₜ` and its point `graphonHomPoint W : PositiveHomSpace ∅ₜ`;
* `graphonHom_coe` — the defining value identity;
* `graphonHom_edge` — the sanity link to the kernel layer: `φ_W` of the unlabelled edge is
  the edge density `p = ∫∫ W` of `GraphonBasic`.
-/

open Classical Finset

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

/-! ## The profile -/

/-- The value of `φ_W` on a sized flag `F`: the total induced density of the labelled graphs
in the isomorphism class `F` — the probability that a `W`-random graph on `F.1` samples is
isomorphic to `F`. -/
noncomputable def graphonProfileFun (W : Graphon) (F : FinFlag ∅ₜ) : ℝ :=
  ∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin F.1) => graphFlag H = F.2),
    graphonFlagDensity W H

lemma graphonProfileFun_nonneg (W : Graphon) (F : FinFlag ∅ₜ) :
    0 ≤ graphonProfileFun W F :=
  Finset.sum_nonneg fun H _ => graphonFlagDensity_nonneg W H

lemma graphonProfileFun_le_one (W : Graphon) (F : FinFlag ∅ₜ) :
    graphonProfileFun W F ≤ 1 := by
  -- The filtered sum is at most the full sum `sum_graphonFlagDensity W F.1 = 1`
  -- (all summands nonnegative).
  unfold graphonProfileFun
  calc ∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin F.1) => graphFlag H = F.2),
        graphonFlagDensity W H
      ≤ ∑ H : SimpleGraph (Fin F.1), graphonFlagDensity W H :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun H _ _ => graphonFlagDensity_nonneg W H)
    _ = 1 := sum_graphonFlagDensity W F.1

/-- The `φ_W` profile packaged in the density-profile space. -/
noncomputable def graphonProfile (W : Graphon) : FlagDensitySpace ∅ₜ :=
  ⟨graphonProfileFun W, by
    simp only [FlagDensitySpace, Set.pi_univ_Icc, Set.mem_Icc]
    exact ⟨fun F => graphonProfileFun_nonneg W F, fun F => graphonProfileFun_le_one W F⟩⟩

@[simp]
theorem graphonProfile_apply (W : Graphon) (F : FinFlag ∅ₜ) :
    (graphonProfile W : FinFlag ∅ₜ → ℝ) F = graphonProfileFun W F := rfl

/-! ## The three structural properties -/

/-- The single graph on no vertices (the bottom/empty graph on `Fin 0`, definitionally the
`emptyType` type itself) has `graphFlag` equal to the empty flag: both the graph component
and the vacuous type embedding are forced by `Fin 0` being empty. -/
private lemma graphFlag_bot_eq_emptyFlag : graphFlag (⊥ : SimpleGraph (Fin 0)) = emptyFlag ∅ₜ :=
  Quotient.sound ((flagEqv_emptyType_iff _ _).mpr ⟨SimpleGraph.Iso.refl⟩)

theorem graphonProfile_oneProp (W : Graphon) : oneProp (graphonProfile W) := by
  -- `(1 : FinFlag ∅ₜ) = ⟨0, emptyFlag ∅ₜ⟩`; `SimpleGraph (Fin 0)` is a subsingleton whose
  -- unique element maps to the unit flag, and its density is `1`
  -- (`graphonFlagDensity_fin_zero`).
  show graphonProfileFun W (1 : FinFlag ∅ₜ) = 1
  unfold graphonProfileFun
  have hsingle : (Finset.univ.filter
      (fun H : SimpleGraph (Fin (1 : FinFlag ∅ₜ).1) => graphFlag H = (1 : FinFlag ∅ₜ).2))
      = {⊥} := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [finFlag_one_snd]
    haveI hsub : Subsingleton (SimpleGraph (Fin (1 : FinFlag ∅ₜ).1)) := by
      rw [finFlag_one_fst]; infer_instance
    constructor
    · intro _; exact Subsingleton.elim H ⊥
    · rintro rfl; exact graphFlag_bot_eq_emptyFlag
  rw [hsingle, Finset.sum_singleton]
  exact graphonFlagDensity_fin_zero W ⊥

/-- A sum of an indicator (`0`/constant `c`) over a `Fintype` is the count of the true set
times the constant. -/
private lemma sum_ite_const {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] (c : ℝ) :
    ∑ _x : α, (if P _x then c else 0) = (Finset.univ.filter P).card * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- **Averaging over embeddings**: the labelled sum picking out the fibre of `graphFlag ∘ comap`
over a fixed target flag does not depend on which embedding `Fin n ↪ Fin ℓ` is used to restrict
along, since any two differ by a permutation of `Fin ℓ` (`exists_perm_comp_emb`) and both the
flag class (`graphFlag_comap_equiv`-style reindexing) and the density
(`graphonFlagDensity_comap_equiv`) are invariant under precomposing with that permutation. -/
private lemma sum_density_comap_embedding_eq (W : Graphon) {n ℓ : ℕ} (F2 : Flag ∅ₜ (Fin n))
    (j1 j2 : Fin n ↪ Fin ℓ) :
    ∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag (Hp.comap ⇑j1) = F2 then graphonFlagDensity W Hp else 0)
      = ∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag (Hp.comap ⇑j2) = F2 then graphonFlagDensity W Hp else 0) := by
  obtain ⟨π, hπ⟩ := exists_perm_comp_emb j2 j1
  have hcomp : (⇑π.symm ∘ ⇑j1 : Fin n → Fin ℓ) = ⇑j2 := by
    funext i
    show π.symm (j1 i) = j2 i
    rw [← hπ i, Equiv.symm_apply_apply]
  have hgraph : ∀ Hp : SimpleGraph (Fin ℓ), Hp.comap ⇑j2 = (Hp.comap ⇑π.symm).comap ⇑j1 := by
    intro Hp
    rw [SimpleGraph.comap_comap, hcomp]
  have step1 : (∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag (Hp.comap ⇑j2) = F2 then graphonFlagDensity W Hp else 0))
      = ∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag ((Hp.comap ⇑π.symm).comap ⇑j1) = F2 then graphonFlagDensity W Hp else 0) :=
    Finset.sum_congr rfl (fun Hp _ => by rw [hgraph Hp])
  rw [step1]
  have step2 : (∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag ((Hp.comap ⇑π.symm).comap ⇑j1) = F2
          then graphonFlagDensity W Hp else 0))
      = ∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag ((Hp.comap ⇑π.symm).comap ⇑j1) = F2
          then graphonFlagDensity W (Hp.comap ⇑π.symm) else 0) :=
    Finset.sum_congr rfl (fun Hp _ => by rw [graphonFlagDensity_comap_equiv W π.symm Hp])
  rw [step2]
  exact (Equiv.sum_comp (graphComapEquiv π.symm)
    (fun Hp' => if graphFlag (Hp'.comap ⇑j1) = F2 then graphonFlagDensity W Hp' else 0)).symm

/-- A vertex subset inducing a copy of an `n`-vertex graph has cardinality `n` (isomorphic
graphs have the same vertex count). -/
private lemma card_eq_of_induce_iso {ℓ n : ℕ} {Hp : SimpleGraph (Fin ℓ)} {Frep : SimpleGraph (Fin n)}
    {S : Finset (Fin ℓ)} (e : Nonempty (Hp.induce (↑S : Set (Fin ℓ)) ≃g Frep)) : S.card = n := by
  obtain ⟨f⟩ := e
  have hc := f.card_eq
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    Set.ncard_coe_finset] at hc
  exact hc

/-- **The counting bridge**: for a vertex subset `S` of size `n`, the subset-induced-iso
condition matches the flag-class condition at the order embedding of `S`.

Proof route: `comap_iso_induce_range` identifies `Hp.comap (S.orderEmbOfFin hS)` with
`Hp.induce ↑S` (`range_orderEmbOfFin`); transport the target iso condition through this fixed
iso and through `graphFlag_eq_iff`. -/
private lemma induce_iso_iff_comap_eq {n ℓ : ℕ} {F2 : Flag ∅ₜ (Fin n)} {Frep : SimpleGraph (Fin n)}
    (hFrep : graphFlag Frep = F2) (Hp : SimpleGraph (Fin ℓ)) (S : Finset (Fin ℓ))
    (hS : S.card = n) :
    Nonempty (Hp.induce (↑S : Set (Fin ℓ)) ≃g Frep)
      ↔ graphFlag (Hp.comap ⇑(S.orderEmbOfFin hS).toEmbedding) = F2 := by
  obtain ⟨e⟩ := comap_iso_induce_range Hp (S.orderEmbOfFin hS).toEmbedding
  rw [RelEmbedding.coe_toEmbedding, Finset.range_orderEmbOfFin] at e
  rw [← hFrep, graphFlag_eq_iff]
  constructor
  · rintro ⟨f⟩; exact ⟨e.trans f⟩
  · rintro ⟨g⟩; exact ⟨e.symm.trans g⟩

/-- **The chain-rule core**: the labelled sum picking out the fibre of `graphFlag ∘ comap
(Fin.castLE h)` over `F2` equals the density-weighted sum over larger unlabelled flags.

Proof route: sum the subset-membership indicator `Nonempty (Hp.induce ↑S ≃g Frep)` over all
`S : Finset (Fin ℓ)` and all `Hp` in two different orders. Summing `Hp` first (for a fixed
`S`) gives either `0` (if `S.card ≠ n`, forced by `card_eq_of_induce_iso`) or, via
`induce_iso_iff_comap_eq` and the averaging lemma `sum_density_comap_embedding_eq`, the fixed
value at `Fin.castLE h`; summing over the `ℓ.choose n` subsets of size `n`
(`Finset.card_powersetCard`) gives `ℓ.choose n` copies of that value. Summing `S` first (for a
fixed `Hp`) gives, via `flagDensity₁_graphFlag`, `ℓ.choose n * flagDensity₁ F2 (graphFlag Hp)`
copies of `graphonFlagDensity W Hp`. Equating the two totals and cancelling `ℓ.choose n ≠ 0`
gives the value at `Fin.castLE h`; regroup by flag class (`Finset.sum_fiberwise`) to land on
`graphonProfileFun`. -/
private lemma graphonProfile_zeroSpace_aux (W : Graphon) {n ℓ : ℕ} (h : n ≤ ℓ)
    (F2 : Flag ∅ₜ (Fin n)) :
    (∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag (Hp.comap (Fin.castLE h)) = F2 then graphonFlagDensity W Hp else 0))
      = ∑ G : FlagWithSize ∅ₜ ℓ, (flagDensity₁ F2 G : ℝ) * graphonProfileFun W ⟨ℓ, G⟩ := by
  set Frep : SimpleGraph (Fin n) := F2.out.graph with hFrepdef
  have hFrep : graphFlag Frep = F2 := graphFlag_out F2
  set sVal : ℝ := ∑ Hp : SimpleGraph (Fin ℓ),
      (if graphFlag (Hp.comap (Fin.castLE h)) = F2 then graphonFlagDensity W Hp else 0)
      with hsValdef
  have hchoose_pos : 0 < ℓ.choose n := Nat.choose_pos h
  have hchoose_ne : (ℓ.choose n : ℝ) ≠ 0 := by exact_mod_cast hchoose_pos.ne'
  -- Summing over `Hp` first, for a fixed `S`.
  have hT_S : ∀ S : Finset (Fin ℓ),
      (∑ Hp : SimpleGraph (Fin ℓ),
        (if Nonempty (Hp.induce (↑S : Set (Fin ℓ)) ≃g Frep) then graphonFlagDensity W Hp else 0))
      = if S.card = n then sVal else 0 := by
    intro S
    by_cases hcard : S.card = n
    · rw [if_pos hcard, hsValdef]
      have hcastLE : (Fin.castLE h : Fin n → Fin ℓ) = ⇑(Fin.castLEEmb h) := rfl
      rw [hcastLE,
        sum_density_comap_embedding_eq W F2 (Fin.castLEEmb h) (S.orderEmbOfFin hcard).toEmbedding]
      exact Finset.sum_congr rfl
        (fun Hp _ => by rw [eq_iff_iff.mpr (induce_iso_iff_comap_eq hFrep Hp S hcard)])
    · rw [if_neg hcard]
      apply Finset.sum_eq_zero
      intro Hp _
      exact if_neg (fun hiso => hcard (card_eq_of_induce_iso hiso))
  -- The double sum over `(S, Hp)`, computed by summing `S` last.
  have hT1 : (∑ S : Finset (Fin ℓ), ∑ Hp : SimpleGraph (Fin ℓ),
        (if Nonempty (Hp.induce (↑S : Set (Fin ℓ)) ≃g Frep) then graphonFlagDensity W Hp else 0))
      = (ℓ.choose n : ℝ) * sVal := by
    calc ∑ S : Finset (Fin ℓ), ∑ Hp : SimpleGraph (Fin ℓ),
          (if Nonempty (Hp.induce (↑S : Set (Fin ℓ)) ≃g Frep) then graphonFlagDensity W Hp else 0)
        = ∑ S : Finset (Fin ℓ), (if S.card = n then sVal else 0) :=
          Finset.sum_congr rfl (fun S _ => hT_S S)
      _ = ((Finset.univ.filter (fun S : Finset (Fin ℓ) => S.card = n)).card : ℝ) * sVal :=
          sum_ite_const _ _
      _ = (ℓ.choose n : ℝ) * sVal := by
          have hset : (Finset.univ.filter (fun S : Finset (Fin ℓ) => S.card = n))
              = Finset.powersetCard n (Finset.univ : Finset (Fin ℓ)) := by
            rw [Finset.powersetCard_eq_filter]; simp
          rw [hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- The double sum over `(S, Hp)`, computed by summing `Hp` last.
  have hT2 : (∑ S : Finset (Fin ℓ), ∑ Hp : SimpleGraph (Fin ℓ),
        (if Nonempty (Hp.induce (↑S : Set (Fin ℓ)) ≃g Frep) then graphonFlagDensity W Hp else 0))
      = (ℓ.choose n : ℝ) * ∑ Hp : SimpleGraph (Fin ℓ),
          (flagDensity₁ F2 (graphFlag Hp) : ℝ) * graphonFlagDensity W Hp := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Hp _
    rw [sum_ite_const]
    have hden := flagDensity₁_graphFlag Frep Hp
    rw [hFrep] at hden
    have hcount : ((Finset.univ.filter
          (fun S : Finset (Fin ℓ) => Nonempty (Hp.induce (↑S : Set (Fin ℓ)) ≃g Frep))).card : ℚ)
        = flagDensity₁ F2 (graphFlag Hp) * (ℓ.choose n : ℚ) := by
      rw [hden]; field_simp
    have hcount_real : ((Finset.univ.filter
          (fun S : Finset (Fin ℓ) => Nonempty (Hp.induce (↑S : Set (Fin ℓ)) ≃g Frep))).card : ℝ)
        = (flagDensity₁ F2 (graphFlag Hp) : ℝ) * (ℓ.choose n : ℝ) := by exact_mod_cast hcount
    rw [hcount_real]; ring
  have hsVal_eq : sVal = ∑ Hp : SimpleGraph (Fin ℓ),
      (flagDensity₁ F2 (graphFlag Hp) : ℝ) * graphonFlagDensity W Hp :=
    mul_left_cancel₀ hchoose_ne (hT1.symm.trans hT2)
  rw [hsVal_eq]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (SimpleGraph (Fin ℓ))) graphFlag
      (fun Hp => (flagDensity₁ F2 (graphFlag Hp) : ℝ) * graphonFlagDensity W Hp)]
  apply Finset.sum_congr rfl
  intro G _
  have hrw : ∀ Hp ∈ Finset.univ.filter (fun Hp : SimpleGraph (Fin ℓ) => graphFlag Hp = G),
      (flagDensity₁ F2 (graphFlag Hp) : ℝ) * graphonFlagDensity W Hp
        = (flagDensity₁ F2 G : ℝ) * graphonFlagDensity W Hp := by
    intro Hp hHp; rw [(Finset.mem_filter.mp hHp).2]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  rfl

theorem graphonProfile_zeroSpaceProp (W : Graphon) : zeroSpaceProp (graphonProfile W) := by
  -- The chain rule, by the extension-partition + subset-averaging scheme of the module
  -- docstring.
  intro F ℓ hℓ
  show graphonProfileFun W F
      = ∑ G : FlagWithSize ∅ₜ ℓ, (flagDensity₁ F.2 G : ℝ) * graphonProfileFun W ⟨ℓ, G⟩
  rw [← graphonProfile_zeroSpace_aux W hℓ F.2]
  show (∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin F.1) => graphFlag H = F.2),
        graphonFlagDensity W H)
      = ∑ Hp : SimpleGraph (Fin ℓ),
          (if graphFlag (Hp.comap (Fin.castLE hℓ)) = F.2 then graphonFlagDensity W Hp else 0)
  rw [Finset.sum_congr rfl (fun H _ => graphonFlagDensity_extension_sum W hℓ H)]
  rw [show (∑ H ∈ Finset.univ.filter (fun H : SimpleGraph (Fin F.1) => graphFlag H = F.2),
        ∑ Hp ∈ Finset.univ.filter (fun Hp : SimpleGraph (Fin ℓ) => Hp.comap (Fin.castLE hℓ) = H),
          graphonFlagDensity W Hp)
      = ∑ Hp ∈ Finset.univ.filter (fun Hp : SimpleGraph (Fin ℓ) =>
          Hp.comap (Fin.castLE hℓ) ∈ Finset.univ.filter
            (fun H : SimpleGraph (Fin F.1) => graphFlag H = F.2)),
          graphonFlagDensity W Hp
      from Finset.sum_fiberwise_eq_sum_filter _ _ _ _]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext Hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro Hp _; rfl

/-- The ranges of the two block embeddings `Fin.castAdd`/`Fin.natAdd` into `Fin (n1+n2)` are
disjoint: `castAdd`-images have value `< n1`, `natAdd`-images have value `≥ n1`. -/
private lemma range_castAdd_disjoint_range_natAdd (n1 n2 : ℕ) :
    Disjoint (Set.range (⇑(Fin.castAddEmb n2 : Fin n1 ↪ Fin (n1 + n2))))
      (Set.range (⇑(Fin.natAddEmb n1 : Fin n2 ↪ Fin (n1 + n2)))) := by
  rw [Set.disjoint_left]
  rintro x ⟨i, rfl⟩ ⟨j, hji⟩
  have h1 : ((Fin.castAddEmb n2 i : Fin (n1 + n2)) : ℕ) = (i : ℕ) := rfl
  have h2 : ((Fin.natAddEmb n1 j : Fin (n1 + n2)) : ℕ) = n1 + (j : ℕ) := rfl
  have heq := congrArg (Fin.val) hji
  rw [h1, h2] at heq
  have hi : i.val < n1 := i.isLt
  omega

/-- **Averaging over pairs of embeddings**: the pair analogue of
`sum_density_comap_embedding_eq`, using `exists_perm_comp_emb_pair`. -/
private lemma sum_density_comap_embedding_pair_eq (W : Graphon) {n1 n2 ℓ : ℕ}
    (F1 : Flag ∅ₜ (Fin n1)) (F2 : Flag ∅ₜ (Fin n2))
    (j1 k1 : Fin n1 ↪ Fin ℓ) (j2 k2 : Fin n2 ↪ Fin ℓ)
    (hj : Disjoint (Set.range ⇑j1) (Set.range ⇑j2))
    (hk : Disjoint (Set.range ⇑k1) (Set.range ⇑k2)) :
    ∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag (Hp.comap ⇑j1) = F1 ∧ graphFlag (Hp.comap ⇑j2) = F2
          then graphonFlagDensity W Hp else 0)
      = ∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag (Hp.comap ⇑k1) = F1 ∧ graphFlag (Hp.comap ⇑k2) = F2
          then graphonFlagDensity W Hp else 0) := by
  obtain ⟨π, hπ1, hπ2⟩ := exists_perm_comp_emb_pair k1 j1 k2 j2 hk hj
  have hcomp1 : (⇑π.symm ∘ ⇑j1 : Fin n1 → Fin ℓ) = ⇑k1 := by
    funext i; show π.symm (j1 i) = k1 i; rw [← hπ1 i, Equiv.symm_apply_apply]
  have hcomp2 : (⇑π.symm ∘ ⇑j2 : Fin n2 → Fin ℓ) = ⇑k2 := by
    funext i; show π.symm (j2 i) = k2 i; rw [← hπ2 i, Equiv.symm_apply_apply]
  have hgraph1 : ∀ Hp : SimpleGraph (Fin ℓ), Hp.comap ⇑k1 = (Hp.comap ⇑π.symm).comap ⇑j1 := by
    intro Hp; rw [SimpleGraph.comap_comap, hcomp1]
  have hgraph2 : ∀ Hp : SimpleGraph (Fin ℓ), Hp.comap ⇑k2 = (Hp.comap ⇑π.symm).comap ⇑j2 := by
    intro Hp; rw [SimpleGraph.comap_comap, hcomp2]
  have step1 : (∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag (Hp.comap ⇑k1) = F1 ∧ graphFlag (Hp.comap ⇑k2) = F2
          then graphonFlagDensity W Hp else 0))
      = ∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag ((Hp.comap ⇑π.symm).comap ⇑j1) = F1
            ∧ graphFlag ((Hp.comap ⇑π.symm).comap ⇑j2) = F2
          then graphonFlagDensity W Hp else 0) :=
    Finset.sum_congr rfl (fun Hp _ => by rw [hgraph1 Hp, hgraph2 Hp])
  rw [step1]
  have step2 : (∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag ((Hp.comap ⇑π.symm).comap ⇑j1) = F1
            ∧ graphFlag ((Hp.comap ⇑π.symm).comap ⇑j2) = F2
          then graphonFlagDensity W Hp else 0))
      = ∑ Hp : SimpleGraph (Fin ℓ),
        (if graphFlag ((Hp.comap ⇑π.symm).comap ⇑j1) = F1
            ∧ graphFlag ((Hp.comap ⇑π.symm).comap ⇑j2) = F2
          then graphonFlagDensity W (Hp.comap ⇑π.symm) else 0) :=
    Finset.sum_congr rfl (fun Hp _ => by rw [graphonFlagDensity_comap_equiv W π.symm Hp])
  rw [step2]
  exact (Equiv.sum_comp (graphComapEquiv π.symm)
    (fun Hp' => if graphFlag (Hp'.comap ⇑j1) = F1 ∧ graphFlag (Hp'.comap ⇑j2) = F2
      then graphonFlagDensity W Hp' else 0)).symm

/-- Regroup a triple sum (two labels + the underlying index) picking out the fibre of a pair
`(g1, g2)` over `t1 × t2` into a single filtered sum. -/
private lemma sum_double_fiberwise {ι κ1 κ2 : Type*} [Fintype ι] [DecidableEq κ1] [DecidableEq κ2]
    (t1 : Finset κ1) (t2 : Finset κ2) (g1 : ι → κ1) (g2 : ι → κ2) (f : ι → ℝ) :
    (∑ j1 ∈ t1, ∑ j2 ∈ t2,
        ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => g1 i = j1 ∧ g2 i = j2), f i)
      = ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => g1 i ∈ t1 ∧ g2 i ∈ t2), f i := by
  have step1 : ∀ j1 : κ1,
      (∑ j2 ∈ t2, ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => g1 i = j1 ∧ g2 i = j2), f i)
      = ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => g1 i = j1 ∧ g2 i ∈ t2), f i := by
    intro j1
    have hfilt : ∀ j2 : κ2, (Finset.univ : Finset ι).filter (fun i => g1 i = j1 ∧ g2 i = j2)
        = ((Finset.univ : Finset ι).filter (fun i => g1 i = j1)).filter (fun i => g2 i = j2) :=
      fun j2 => (Finset.filter_filter _ _ _).symm
    simp_rw [hfilt]
    rw [Finset.sum_fiberwise_eq_sum_filter, Finset.filter_filter]
  rw [Finset.sum_congr rfl (fun j1 _ => step1 j1)]
  have hswap : ∀ j1 : κ1, (Finset.univ : Finset ι).filter (fun i => g1 i = j1 ∧ g2 i ∈ t2)
      = ((Finset.univ : Finset ι).filter (fun i => g2 i ∈ t2)).filter (fun i => g1 i = j1) := by
    intro j1
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun i _ => and_comm)
  simp_rw [hswap]
  rw [Finset.sum_fiberwise_eq_sum_filter, Finset.filter_filter]
  exact Finset.sum_congr (Finset.filter_congr (fun i _ => and_comm)) (fun _ _ => rfl)

/-- **The block-product chain-rule core**: the pair analogue of `graphonProfile_zeroSpace_aux`.
-/
private lemma graphonProfile_mul_aux (W : Graphon) {n1 n2 : ℕ}
    (F1 : Flag ∅ₜ (Fin n1)) (F2 : Flag ∅ₜ (Fin n2)) :
    (∑ Hp : SimpleGraph (Fin (n1 + n2)),
        (if graphFlag (Hp.comap (Fin.castAdd n2)) = F1 ∧ graphFlag (Hp.comap (Fin.natAdd n1)) = F2
          then graphonFlagDensity W Hp else 0))
      = ∑ G : FlagWithSize ∅ₜ (n1 + n2),
          (flagDensity₂ F1 F2 G : ℝ) * graphonProfileFun W ⟨n1 + n2, G⟩ := by
  set Frep1 : SimpleGraph (Fin n1) := F1.out.graph with hFrep1def
  set Frep2 : SimpleGraph (Fin n2) := F2.out.graph with hFrep2def
  have hFrep1 : graphFlag Frep1 = F1 := graphFlag_out F1
  have hFrep2 : graphFlag Frep2 = F2 := graphFlag_out F2
  set sVal : ℝ := ∑ Hp : SimpleGraph (Fin (n1 + n2)),
      (if graphFlag (Hp.comap (Fin.castAdd n2)) = F1 ∧ graphFlag (Hp.comap (Fin.natAdd n1)) = F2
        then graphonFlagDensity W Hp else 0) with hsValdef
  have hchoose_pos : 0 < (n1 + n2).choose n1 := Nat.choose_pos (Nat.le_add_right n1 n2)
  have hchoose_ne : ((n1 + n2).choose n1 : ℝ) ≠ 0 := by exact_mod_cast hchoose_pos.ne'
  have hdisjCA_NA := range_castAdd_disjoint_range_natAdd n1 n2
  have hT_S1 : ∀ S1 : Finset (Fin (n1 + n2)),
      (∑ Hp : SimpleGraph (Fin (n1 + n2)),
        (if Nonempty (Hp.induce (↑S1 : Set (Fin (n1 + n2))) ≃g Frep1)
            ∧ Nonempty (Hp.induce (↑S1ᶜ : Set (Fin (n1 + n2))) ≃g Frep2)
          then graphonFlagDensity W Hp else 0))
      = if S1.card = n1 then sVal else 0 := by
    intro S1
    by_cases hcard : S1.card = n1
    · rw [if_pos hcard, hsValdef]
      have hcard2 : S1ᶜ.card = n2 := by
        rw [Finset.card_compl, hcard, Fintype.card_fin]; omega
      have hdisj12 : Disjoint (↑S1 : Set (Fin (n1 + n2))) (↑S1ᶜ : Set (Fin (n1 + n2))) := by
        rw [Finset.disjoint_coe]; exact disjoint_compl_right
      have hrange_j : Set.range ⇑(S1.orderEmbOfFin hcard).toEmbedding
          = (↑S1 : Set (Fin (n1 + n2))) := by
        rw [RelEmbedding.coe_toEmbedding]; exact Finset.range_orderEmbOfFin S1 hcard
      have hrange_k : Set.range ⇑(S1ᶜ.orderEmbOfFin hcard2).toEmbedding
          = (↑S1ᶜ : Set (Fin (n1 + n2))) := by
        rw [RelEmbedding.coe_toEmbedding]; exact Finset.range_orderEmbOfFin S1ᶜ hcard2
      have hdisj_jk : Disjoint (Set.range ⇑(S1.orderEmbOfFin hcard).toEmbedding)
          (Set.range ⇑(S1ᶜ.orderEmbOfFin hcard2).toEmbedding) := by
        rw [hrange_j, hrange_k]; exact hdisj12
      have hmain := sum_density_comap_embedding_pair_eq W F1 F2
        (Fin.castAddEmb n2) (S1.orderEmbOfFin hcard).toEmbedding
        (Fin.natAddEmb n1) (S1ᶜ.orderEmbOfFin hcard2).toEmbedding hdisjCA_NA hdisj_jk
      rw [show (Fin.castAdd n2 : Fin n1 → Fin (n1 + n2)) = ⇑(Fin.castAddEmb n2) from rfl,
        show (Fin.natAdd n1 : Fin n2 → Fin (n1 + n2)) = ⇑(Fin.natAddEmb n1) from rfl, hmain]
      apply Finset.sum_congr rfl
      intro Hp _
      congr 1
      rw [eq_iff_iff]
      exact and_congr (induce_iso_iff_comap_eq hFrep1 Hp S1 hcard)
        (induce_iso_iff_comap_eq hFrep2 Hp S1ᶜ hcard2)
    · rw [if_neg hcard]
      apply Finset.sum_eq_zero
      intro Hp _
      apply if_neg
      rintro ⟨h1, _⟩
      exact hcard (card_eq_of_induce_iso h1)
  have hT1 : (∑ S1 : Finset (Fin (n1 + n2)), ∑ Hp : SimpleGraph (Fin (n1 + n2)),
        (if Nonempty (Hp.induce (↑S1 : Set (Fin (n1 + n2))) ≃g Frep1)
            ∧ Nonempty (Hp.induce (↑S1ᶜ : Set (Fin (n1 + n2))) ≃g Frep2)
          then graphonFlagDensity W Hp else 0))
      = ((n1 + n2).choose n1 : ℝ) * sVal := by
    calc ∑ S1 : Finset (Fin (n1 + n2)), ∑ Hp : SimpleGraph (Fin (n1 + n2)),
          (if Nonempty (Hp.induce (↑S1 : Set (Fin (n1 + n2))) ≃g Frep1)
              ∧ Nonempty (Hp.induce (↑S1ᶜ : Set (Fin (n1 + n2))) ≃g Frep2)
            then graphonFlagDensity W Hp else 0)
        = ∑ S1 : Finset (Fin (n1 + n2)), (if S1.card = n1 then sVal else 0) :=
          Finset.sum_congr rfl (fun S1 _ => hT_S1 S1)
      _ = ((Finset.univ.filter
            (fun S1 : Finset (Fin (n1 + n2)) => S1.card = n1)).card : ℝ) * sVal :=
          sum_ite_const _ _
      _ = ((n1 + n2).choose n1 : ℝ) * sVal := by
          have hset : (Finset.univ.filter (fun S1 : Finset (Fin (n1 + n2)) => S1.card = n1))
              = Finset.powersetCard n1 (Finset.univ : Finset (Fin (n1 + n2))) := by
            rw [Finset.powersetCard_eq_filter]; simp
          rw [hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hT2 : (∑ S1 : Finset (Fin (n1 + n2)), ∑ Hp : SimpleGraph (Fin (n1 + n2)),
        (if Nonempty (Hp.induce (↑S1 : Set (Fin (n1 + n2))) ≃g Frep1)
            ∧ Nonempty (Hp.induce (↑S1ᶜ : Set (Fin (n1 + n2))) ≃g Frep2)
          then graphonFlagDensity W Hp else 0))
      = ((n1 + n2).choose n1 : ℝ) * ∑ Hp : SimpleGraph (Fin (n1 + n2)),
          (flagDensity₂ F1 F2 (graphFlag Hp) : ℝ) * graphonFlagDensity W Hp := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Hp _
    rw [sum_ite_const]
    have hpairbij : (Finset.univ.filter (fun S1 : Finset (Fin (n1 + n2)) =>
          Nonempty (Hp.induce (↑S1 : Set (Fin (n1 + n2))) ≃g Frep1)
            ∧ Nonempty (Hp.induce (↑S1ᶜ : Set (Fin (n1 + n2))) ≃g Frep2))).card
        = (Finset.univ.filter (fun P : Finset (Fin (n1 + n2)) × Finset (Fin (n1 + n2)) =>
            Disjoint P.1 P.2 ∧ Nonempty (Hp.induce (↑P.1 : Set (Fin (n1 + n2))) ≃g Frep1)
              ∧ Nonempty (Hp.induce (↑P.2 : Set (Fin (n1 + n2))) ≃g Frep2))).card := by
      apply Finset.card_bij (fun S1 _ => (S1, S1ᶜ))
      · intro S1 hS1
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS1 ⊢
        exact ⟨disjoint_compl_right, hS1.1, hS1.2⟩
      · intro S1 _ S1' _ heq
        exact (Prod.mk.injEq .. |>.mp heq).1
      · intro P hP
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
        obtain ⟨hdisj, hiso1, hiso2⟩ := hP
        have hcard1 : P.1.card = n1 := card_eq_of_induce_iso hiso1
        have hsub : P.2 ⊆ P.1ᶜ := by
          intro x hx
          simp only [Finset.mem_compl]
          exact fun hx1 => Finset.disjoint_left.mp hdisj hx1 hx
        have hcard2 : P.2.card = n2 := card_eq_of_induce_iso hiso2
        have hcardcompl : P.1ᶜ.card = n2 := by
          rw [Finset.card_compl, hcard1, Fintype.card_fin]; omega
        have hP2eq : P.2 = P.1ᶜ :=
          Finset.eq_of_subset_of_card_le hsub (by rw [hcardcompl, hcard2])
        refine ⟨P.1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hiso1, hP2eq ▸ hiso2⟩
        · exact Prod.ext rfl hP2eq.symm
    have hden := flagDensity₂_graphFlag Frep1 Frep2 Hp
    rw [hFrep1, hFrep2] at hden
    have hcount : ((Finset.univ.filter
          (fun P : Finset (Fin (n1 + n2)) × Finset (Fin (n1 + n2)) =>
            Disjoint P.1 P.2 ∧ Nonempty (Hp.induce (↑P.1 : Set (Fin (n1 + n2))) ≃g Frep1)
              ∧ Nonempty (Hp.induce (↑P.2 : Set (Fin (n1 + n2))) ≃g Frep2))).card : ℚ)
        = flagDensity₂ F1 F2 (graphFlag Hp) * ((n1 + n2).choose n1 : ℚ) := by
      rw [hden]; field_simp
    have hcount_real : ((Finset.univ.filter
          (fun S1 : Finset (Fin (n1 + n2)) =>
            Nonempty (Hp.induce (↑S1 : Set (Fin (n1 + n2))) ≃g Frep1)
              ∧ Nonempty (Hp.induce (↑S1ᶜ : Set (Fin (n1 + n2))) ≃g Frep2))).card : ℝ)
        = (flagDensity₂ F1 F2 (graphFlag Hp) : ℝ) * ((n1 + n2).choose n1 : ℝ) := by
      rw [hpairbij]; exact_mod_cast hcount
    rw [hcount_real]; ring
  have hsVal_eq : sVal = ∑ Hp : SimpleGraph (Fin (n1 + n2)),
      (flagDensity₂ F1 F2 (graphFlag Hp) : ℝ) * graphonFlagDensity W Hp :=
    mul_left_cancel₀ hchoose_ne (hT1.symm.trans hT2)
  rw [hsVal_eq]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (SimpleGraph (Fin (n1 + n2)))) graphFlag
      (fun Hp => (flagDensity₂ F1 F2 (graphFlag Hp) : ℝ) * graphonFlagDensity W Hp)]
  apply Finset.sum_congr rfl
  intro G _
  have hrw : ∀ Hp ∈ Finset.univ.filter (fun Hp : SimpleGraph (Fin (n1 + n2)) => graphFlag Hp = G),
      (flagDensity₂ F1 F2 (graphFlag Hp) : ℝ) * graphonFlagDensity W Hp
        = (flagDensity₂ F1 F2 G : ℝ) * graphonFlagDensity W Hp := by
    intro Hp hHp; rw [(Finset.mem_filter.mp hHp).2]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  rfl

theorem graphonProfile_mulProp (W : Graphon) : mulProp (graphonProfile W) := by
  -- Multiplicativity, by the block-product + pair-averaging scheme of the module docstring.
  intro F1 F2
  show graphonProfileFun W F1 * graphonProfileFun W F2
      = ∑ G : FlagWithSize ∅ₜ (F1.1 + F2.1),
          (flagDensity₂ F1.2 F2.2 G : ℝ) * graphonProfileFun W ⟨F1.1 + F2.1, G⟩
  rw [← graphonProfile_mul_aux W F1.2 F2.2]
  show (∑ H1 ∈ Finset.univ.filter (fun H1 : SimpleGraph (Fin F1.1) => graphFlag H1 = F1.2),
        graphonFlagDensity W H1)
      * (∑ H2 ∈ Finset.univ.filter (fun H2 : SimpleGraph (Fin F2.1) => graphFlag H2 = F2.2),
        graphonFlagDensity W H2)
      = ∑ Hp : SimpleGraph (Fin (F1.1 + F2.1)),
          (if graphFlag (Hp.comap (Fin.castAdd F2.1)) = F1.2
              ∧ graphFlag (Hp.comap (Fin.natAdd F1.1)) = F2.2
            then graphonFlagDensity W Hp else 0)
  rw [Finset.sum_mul_sum]
  rw [show (∑ H1 ∈ Finset.univ.filter (fun H1 : SimpleGraph (Fin F1.1) => graphFlag H1 = F1.2),
        ∑ H2 ∈ Finset.univ.filter (fun H2 : SimpleGraph (Fin F2.1) => graphFlag H2 = F2.2),
          graphonFlagDensity W H1 * graphonFlagDensity W H2)
      = ∑ H1 ∈ Finset.univ.filter (fun H1 : SimpleGraph (Fin F1.1) => graphFlag H1 = F1.2),
        ∑ H2 ∈ Finset.univ.filter (fun H2 : SimpleGraph (Fin F2.1) => graphFlag H2 = F2.2),
          ∑ Hp ∈ Finset.univ.filter (fun Hp : SimpleGraph (Fin (F1.1 + F2.1)) =>
            Hp.comap (Fin.castAdd F2.1) = H1 ∧ Hp.comap (Fin.natAdd F1.1) = H2),
            graphonFlagDensity W Hp
      from Finset.sum_congr rfl (fun H1 _ => Finset.sum_congr rfl
        (fun H2 _ => graphonFlagDensity_block_mul W H1 H2))]
  rw [sum_double_fiberwise]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext Hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro Hp _; rfl

/-! ## The homomorphism -/

/-- **Every graphon is a positive homomorphism**: the limit functional `φ_W` of the graphon
`W` at the empty type. -/
noncomputable def graphonHom (W : Graphon) : PositiveHom ∅ₜ :=
  positiveHomFromZeroSpaceOneMulProp (graphonProfile W)
    (graphonProfile_zeroSpaceProp W) (graphonProfile_oneProp W)
    (graphonProfile_mulProp W)

@[simp]
theorem graphonHom_coe (W : Graphon) (F : FinFlag ∅ₜ) :
    (graphonHom W).coe F = graphonProfileFun W F := by
  show linearExtension (graphonProfile W) (basisVector F) = (graphonProfile W : _) F
  rw [linearExtension_basisVector]

/-- The point of `X_{∅ₜ}` carried by `φ_W`. -/
noncomputable def graphonHomPoint (W : Graphon) : PositiveHomSpace ∅ₜ :=
  posHomPoint (graphonHom W)

/-! ## Sanity link to the kernel layer -/

/-- `φ_W` of the unlabelled edge is the edge density of the graphon: the flag-algebra layer
and the kernel layer of the graphon development agree at the edge.

Proof route: on `Fin 2` the flag class of the edge contains exactly the graph `⊤`
(`graphFlag_eq_iff` + a two-vertex case analysis), so the profile value is
`graphonFlagDensity W ⊤ = W.edgeDensity` (`graphonFlagDensity_top_two`). -/
private lemma simpleGraph_fin2_eq_top_of_adj {H : SimpleGraph (Fin 2)} (h : H.Adj 0 1) :
    H = ⊤ := by
  ext u v
  fin_cases u <;> fin_cases v
  · simp
  · simp [h]
  · simp [h.symm]
  · simp

private lemma graphFlag_eq_edge_iff (H : SimpleGraph (Fin 2)) :
    graphFlag H = unlabelledEdgeFlag ↔ H = ⊤ := by
  unfold unlabelledEdgeFlag
  rw [graphFlag_eq_iff]
  constructor
  · rintro ⟨f⟩
    apply simpleGraph_fin2_eq_top_of_adj
    have htop : (⊤ : SimpleGraph (Fin 2)).Adj (f 0) (f 1) :=
      (SimpleGraph.top_adj (f 0) (f 1)).mpr (f.injective.ne (by decide))
    rwa [f.map_adj_iff] at htop
  · rintro rfl
    exact ⟨SimpleGraph.Iso.refl⟩

theorem graphonHom_edge (W : Graphon) :
    (graphonHom W).coe ⟨2, unlabelledEdgeFlag⟩ = W.edgeDensity := by
  rw [graphonHom_coe]
  show graphonProfileFun W ⟨2, unlabelledEdgeFlag⟩ = W.edgeDensity
  unfold graphonProfileFun
  have hfilter : (Finset.univ.filter
      (fun H : SimpleGraph (Fin (⟨2, unlabelledEdgeFlag⟩ : FinFlag ∅ₜ).1) =>
        graphFlag H = (⟨2, unlabelledEdgeFlag⟩ : FinFlag ∅ₜ).2))
      = {(⊤ : SimpleGraph (Fin 2))} := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact graphFlag_eq_edge_iff H
  rw [hfilter, Finset.sum_singleton]
  exact graphonFlagDensity_top_two W

end FlagAlgebras.MetaTheory
