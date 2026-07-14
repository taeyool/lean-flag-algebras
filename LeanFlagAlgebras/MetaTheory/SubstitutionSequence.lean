import LeanFlagAlgebras.MetaTheory.HeredClass
import LeanFlagAlgebras.MetaTheory.SubstitutionBlowup
import LeanFlagAlgebras.MetaTheory.BlowupSequence

/-! # The uniform generalised-blow-up flag sequence and its base limit (paper §6–§7)

Mirror of `BlowupSequence` for the generalised blow-up `subBlowup`.  Fix a hereditary class `hc`, a
type `σ`, an in-class base graph `Γ` (`hc.Mem Γ`) with `σ ↪g Γ`, and a within-class family
`Wf : (M : ℕ) → ∀ v : Fin n, SimpleGraph (Fin (M+1))` whose uniform `(M+1)`-generalised blow-up of
`Γ` stays in the class (`hclosure`).  This produces the base limit `φ₀` the §6/§7 capstones need:

* `blowupFlagSeq_sub` — the `FlagSeq ∅ₜ` whose `M`-th flag is the unlabelled uniform `(M+1)`-blow-up
  `subBlowup Γ (Wf M)`, presented on `Fin (n·(M+1))`; each flag is in the class (`hclosure`).
* `exists_blowup_limit_sub` — a convergent subsequence with base limit `φ₀ : PositiveHom ∅ₜ`.
* `blowup_limit_mem_Q0_sub` — `posHomPoint φ₀ ∈ Q0` (every blow-up forbidden-free).
* `blowup_limit_type_pos_sub` — `φ₀⟨σ⟩₀ > 0` (uniform `1/n^{n₀}` σ-density lower bound, from the
  planted subset count, which is insensitive to the within-class structure).
-/

open Filter Topology
open SimpleGraph Finset GraphAlgebras

namespace FlagAlgebras.MetaTheory

open FlagAlgebras

attribute [local instance] Classical.propDecidable

variable {n₀ : ℕ}

/-! ## The uniform generalised blow-up, presented on `Fin (n·(M+1))` -/

/-- The uniform `(M+1)`-generalised blow-up of `Γ` with within-class family `Wf M`, presented on
`Fin (n·(M+1))` via `blowupHostEquiv`. -/
noncomputable def subBlowupGraphFin {n : ℕ} (Γ : SimpleGraph (Fin n))
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) (M : ℕ) :
    SimpleGraph (Fin (n * (M + 1))) :=
  SimpleGraph.map (blowupHostEquiv n M).toEmbedding (subBlowup Γ (Wf M))

/-- The presentation iso: the `Σ`-hosted generalised blow-up is isomorphic to its `Fin`-hosted
presentation `subBlowupGraphFin`. -/
noncomputable def subBlowupGraphFin_iso {n : ℕ} (Γ : SimpleGraph (Fin n))
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) (M : ℕ) :
    subBlowup Γ (Wf M) ≃g subBlowupGraphFin Γ Wf M :=
  SimpleGraph.Iso.map (blowupHostEquiv n M) (subBlowup Γ (Wf M))

/-- **Each generalised blow-up presentation is in the class** (the closure hypothesis transported
along the presentation iso by heredity). -/
theorem subBlowupGraphFin_mem (hc : HeredClass) {n : ℕ} {Γ : SimpleGraph (Fin n)}
    {Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))}
    (hclosure : ∀ M, hc.Mem (subBlowup Γ (Wf M))) (M : ℕ) :
    hc.Mem (subBlowupGraphFin Γ Wf M) :=
  hc.comap (subBlowupGraphFin_iso Γ Wf M).symm.toEmbedding (hclosure M)

/-! ## The flag sequence -/

/-- The unlabelled `M`-th flag: the uniform `(M+1)`-generalised blow-up of `Γ` as an `∅ₜ`-flag. -/
noncomputable def blowupFlagSeq_sub {n : ℕ} (Γ : SimpleGraph (Fin n))
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) : FlagSeq ∅ₜ :=
  fun M => ⟨n * (M + 1), graphFlag (subBlowupGraphFin Γ Wf M)⟩

@[simp]
theorem blowupFlagSeq_sub_fst {n : ℕ} (Γ : SimpleGraph (Fin n))
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) (M : ℕ) :
    (blowupFlagSeq_sub Γ Wf M).1 = n * (M + 1) := rfl

@[simp]
theorem blowupFlagSeq_sub_snd {n : ℕ} (Γ : SimpleGraph (Fin n))
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) (M : ℕ) :
    (blowupFlagSeq_sub Γ Wf M).2 = graphFlag (subBlowupGraphFin Γ Wf M) := rfl

theorem blowupFlagSeq_sub_increases {n : ℕ} (hn : 0 < n) (Γ : SimpleGraph (Fin n))
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) :
    Increases (blowupFlagSeq_sub Γ Wf) := by
  apply increases_of_consecutive_lt
  intro M
  simp only [blowupFlagSeq_sub_fst]
  gcongr
  omega

/-! ## The base limit -/

/-- **The base limit** (mirror of §5's `exists_blowup_limit`).  Extracts a convergent subsequence
`blowupFlagSeq_sub Γ Wf ∘ ϕ` of the increasing generalised-blow-up flag sequence, together with its
base limit `φ₀ : PositiveHom ∅ₜ`. -/
theorem exists_blowup_limit_sub {n : ℕ} (hn : 0 < n) (Γ : SimpleGraph (Fin n))
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) :
    ∃ (ϕ : ℕ → ℕ) (φ₀ : PositiveHom ∅ₜ),
      StrictMono ϕ ∧ ConvergesTo (blowupFlagSeq_sub Γ Wf ∘ ϕ) φ₀.coe := by
  obtain ⟨a, ϕ, hϕ, hconv⟩ :=
    increasing_flagSeq_contain_convergent_subseq (blowupFlagSeq_sub Γ Wf)
      (blowupFlagSeq_sub_increases hn Γ Wf)
  obtain ⟨φ₀, hφ₀⟩ := flagSeq_limit_mem_positiveHom (blowupFlagSeq_sub Γ Wf ∘ ϕ) hconv
  exact ⟨ϕ, φ₀, hϕ, hφ₀ ▸ hconv⟩

/-! ## The base limit lies in `Q₀` -/

theorem flagDensity_forbidden_blowupFlagSeq_sub_zero (hc : HeredClass) {n₀ : ℕ}
    {σ : FlagType (Fin n₀)} {n : ℕ} {Γ : SimpleGraph (Fin n)}
    {Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))}
    (hclosure : ∀ M, hc.Mem (subBlowup Γ (Wf M))) (M : ℕ)
    {D : FinFlag ∅ₜ} (hD : (hc.constraintOf σ).forb0 D) :
    flagDensity₁ D.2 (blowupFlagSeq_sub Γ Wf M).2 = 0 := by
  simpa only [blowupFlagSeq_sub_snd] using
    hc.forbiddenFree_of_mem (subBlowupGraphFin Γ Wf M)
      (subBlowupGraphFin_mem hc hclosure M) D hD

theorem blowup_limit_mem_Q0_sub (hc : HeredClass) {n₀ : ℕ} {σ : FlagType (Fin n₀)} {n : ℕ}
    {Γ : SimpleGraph (Fin n)} {Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))}
    (hclosure : ∀ M, hc.Mem (subBlowup Γ (Wf M))) {ϕ : ℕ → ℕ} {φ₀ : PositiveHom ∅ₜ}
    (hconv : ConvergesTo (blowupFlagSeq_sub Γ Wf ∘ ϕ) φ₀.coe) :
    posHomPoint φ₀ ∈ Qσ (hc.constraintOf σ).forb0 := by
  rw [mem_Qσ_iff]
  intro D hD
  rw [posHomPoint_val_apply, ← φ₀.coe_flag D]
  have hlim : Tendsto (fun M => flagDensitySeq (blowupFlagSeq_sub Γ Wf ∘ ϕ) M D) atTop
      (𝓝 (φ₀.coe D)) := (flagSeq_convergesTo_iff.mp hconv).2 D
  have hzero : ∀ M, flagDensitySeq (blowupFlagSeq_sub Γ Wf ∘ ϕ) M D = 0 := by
    intro M
    show (flagDensity₁ D.2 (blowupFlagSeq_sub Γ Wf (ϕ M)).2 : ℝ) = 0
    rw [flagDensity_forbidden_blowupFlagSeq_sub_zero hc hclosure (ϕ M) hD, Rat.cast_zero]
  rw [tendsto_congr hzero, tendsto_const_nhds_iff] at hlim
  exact hlim.symm

/-! ## A uniform positive lower bound on the σ-type density

The σ-type graph is an induced subgraph of every generalised blow-up, with the same uniform lower
bound as in §5: the planted subsets induce copies of `σ`, and the planted iso never sees the
within-class structure (planted vertices lie in distinct clone classes). -/

/-- The planted vertex set induces a copy of `σ` in the generalised blow-up (mirror of §5
`plantedIso`).  Distinct labels go to distinct clone classes, where adjacency is the base value. -/
noncomputable def plantedIso_sub {n : ℕ} {σ : FlagType (Fin n₀)} {Γ : SimpleGraph (Fin n)}
    (θ : σ ↪g Γ) (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) (M : ℕ)
    (c : Fin n₀ → Fin (M + 1)) :
    σ ≃g ((⊤ : (subBlowup Γ (Wf M)).Subgraph).induce (↑(plantedSet θ M c) : Set _)).coe := by
  set B := subBlowup Γ (Wf M)
  set S : Set (Σ v : Fin n, Fin (M + 1)) := ↑(plantedSet θ M c) with hS
  have hmem : ∀ i : Fin n₀, (⟨θ i, c i⟩ : Σ v : Fin n, Fin (M + 1)) ∈ S := by
    intro i
    simp only [hS, plantedSet, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and]
    exact ⟨i, rfl⟩
  let f : Fin n₀ → S := fun i => ⟨⟨θ i, c i⟩, hmem i⟩
  have hf_inj : Function.Injective f := by
    intro i j h
    exact θ.injective (congrArg Sigma.fst (Subtype.ext_iff.mp h))
  have hf_surj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    simp only [hS, plantedSet, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, Subtype.ext hi⟩
  refine ⟨Equiv.ofBijective f ⟨hf_inj, hf_surj⟩, ?_⟩
  intro i j
  simp only [Equiv.ofBijective_apply, Subgraph.coe_adj]
  show ((⊤ : B.Subgraph).induce S).Adj (f i).1 (f j).1 ↔ σ.Adj i j
  by_cases hij : i = j
  · subst hij
    simp only [Subgraph.induce_adj, Subgraph.top_adj, SimpleGraph.irrefl, and_false]
  · have hθ : (θ j) ≠ (θ i) := fun h => hij (θ.injective h.symm)
    simp only [Subgraph.induce_adj, Subgraph.top_adj]
    constructor
    · rintro ⟨_, _, hadj⟩
      rw [show (f i).1 = (⟨θ i, c i⟩ : Σ v, Fin (M+1)) from rfl,
          show (f j).1 = (⟨θ j, c j⟩ : Σ v, Fin (M+1)) from rfl,
          subBlowup_adj_of_fst_ne Γ (Wf M) hθ] at hadj
      exact θ.map_adj_iff.mp hadj
    · intro h
      refine ⟨(f i).2, (f j).2, ?_⟩
      rw [show (f i).1 = (⟨θ i, c i⟩ : Σ v, Fin (M+1)) from rfl,
          show (f j).1 = (⟨θ j, c j⟩ : Σ v, Fin (M+1)) from rfl,
          subBlowup_adj_of_fst_ne Γ (Wf M) hθ]
      exact θ.map_adj_iff.mpr h

/-- **Planted lower bound on the σ-count** (mirror of §5): at least `(M+1)^{n₀}` induced copies of
`σ` in the generalised `(M+1)`-blow-up. -/
theorem pow_le_subgraphCount_subBlowup {n : ℕ} {σ : FlagType (Fin n₀)}
    {Γ : SimpleGraph (Fin n)} (θ : σ ↪g Γ)
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) (M : ℕ) :
    (M + 1) ^ n₀ ≤ subgraphCount σ (subBlowup Γ (Wf M)) := by
  set B := subBlowup Γ (Wf M)
  have hmaps : ∀ c : Fin n₀ → Fin (M + 1),
      (⊤ : B.Subgraph).induce (↑(plantedSet θ M c) : Set _) ∈ subgraphSet σ B := by
    intro c
    rw [mem_subgraphSet_iff]
    exact ⟨Subgraph.induce_top_isInduced _ _, ⟨(plantedIso_sub θ Wf M c).symm⟩⟩
  have hinj : Function.Injective (fun c : Fin n₀ → Fin (M + 1) =>
      (⊤ : B.Subgraph).induce (↑(plantedSet θ M c) : Set _)) := by
    intro c c' h
    have h2 := congrArg Subgraph.verts h
      |>.trans (Subgraph.induce_verts (⊤ : B.Subgraph) (↑(plantedSet θ M c') : Set _))
    rw [Subgraph.induce_verts] at h2
    have hverts : (↑(plantedSet θ M c) : Set (Σ v : Fin n, Fin (M + 1)))
        = (↑(plantedSet θ M c') : Set (Σ v : Fin n, Fin (M + 1))) := h2
    funext i
    have hi : (⟨θ i, c i⟩ : Σ v : Fin n, Fin (M + 1)) ∈
        (↑(plantedSet θ M c) : Set _) := by
      simp only [plantedSet, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
        true_and]
      exact ⟨i, rfl⟩
    rw [hverts] at hi
    simp only [plantedSet, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at hi
    obtain ⟨j, hj⟩ := hi
    have hij : θ j = θ i := (Sigma.mk.inj_iff.mp hj).1
    have heqij : j = i := θ.injective hij
    subst heqij
    exact (eq_of_heq (Sigma.mk.inj_iff.mp hj).2).symm
  calc (M + 1) ^ n₀ = Fintype.card (Fin n₀ → Fin (M + 1)) := by simp
    _ = (Finset.univ : Finset (Fin n₀ → Fin (M + 1))).card := by rw [Finset.card_univ]
    _ = (Finset.univ.image (fun c : Fin n₀ → Fin (M + 1) =>
          (⊤ : B.Subgraph).induce (↑(plantedSet θ M c) : Set _))).card := by
        rw [Finset.card_image_of_injective _ hinj]
    _ ≤ (subgraphSet σ B).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨c, rfl⟩ := hx
        exact hmaps c
    _ = subgraphCount σ B := rfl

theorem subgraphCount_subBlowupGraphFin {n : ℕ} (σ : FlagType (Fin n₀)) (Γ : SimpleGraph (Fin n))
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) (M : ℕ) :
    subgraphCount σ (subBlowupGraphFin Γ Wf M) = subgraphCount σ (subBlowup Γ (Wf M)) :=
  (subgraphCount_eq_of_iso σ (subBlowupGraphFin_iso Γ Wf M)).symm

theorem subgraphDensity_subBlowupGraphFin_lower {n : ℕ} (hn : 0 < n) {σ : FlagType (Fin n₀)}
    {Γ : SimpleGraph (Fin n)} (θ : σ ↪g Γ)
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) (M : ℕ) :
    (1 : ℚ) / (n ^ n₀) ≤ subgraphDensity σ (subBlowupGraphFin Γ Wf M) := by
  have hn0 : n₀ ≤ n := fin_card_le_of_embedding θ
  have hcnt : (M + 1) ^ n₀ ≤ subgraphCount σ (subBlowupGraphFin Γ Wf M) := by
    rw [subgraphCount_subBlowupGraphFin]
    exact pow_le_subgraphCount_subBlowup θ Wf M
  have hcardV : Fintype.card (Fin n₀) = n₀ := Fintype.card_fin n₀
  have hcardW : Fintype.card (Fin (n * (M + 1))) = n * (M + 1) := Fintype.card_fin _
  set cnt := subgraphCount σ (subBlowupGraphFin Γ Wf M) with hcntdef
  have hdens : subgraphDensity σ (subBlowupGraphFin Γ Wf M)
      = (cnt : ℚ) / ((n * (M + 1)).choose n₀) := by
    simp only [subgraphDensity, hcardV, hcardW, hcntdef]
  rw [hdens]
  have hnpos : (0 : ℚ) < ((n ^ n₀ : ℕ) : ℚ) := by positivity
  have hchoose_le : ((n * (M + 1)).choose n₀) ≤ (n * (M + 1)) ^ n₀ := Nat.choose_le_pow _ _
  have hNpow : (n * (M + 1)) ^ n₀ = n ^ n₀ * (M + 1) ^ n₀ := by rw [mul_pow]
  have hn0le : n₀ ≤ n * (M + 1) := le_trans hn0 (Nat.le_mul_of_pos_right n (by omega))
  have hchoose_pos : (0 : ℚ) < (((n * (M + 1)).choose n₀ : ℕ) : ℚ) := by
    exact_mod_cast Nat.choose_pos hn0le
  rw [div_le_div_iff₀ (by exact_mod_cast hnpos) hchoose_pos]
  have key : (((n * (M + 1)).choose n₀ : ℕ) : ℚ) ≤ (cnt : ℚ) * (n : ℚ) ^ n₀ := by
    calc (((n * (M + 1)).choose n₀ : ℕ) : ℚ)
        ≤ (((n * (M + 1)) ^ n₀ : ℕ) : ℚ) := by exact_mod_cast hchoose_le
      _ = (((M + 1) ^ n₀ : ℕ) : ℚ) * (n : ℚ) ^ n₀ := by push_cast [hNpow]; ring
      _ ≤ (cnt : ℚ) * (n : ℚ) ^ n₀ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcnt
  push_cast at key ⊢
  linarith [key]

theorem flagDensity_type_blowupFlagSeq_sub_lower {n : ℕ} (hn : 0 < n) {σ : FlagType (Fin n₀)}
    {Γ : SimpleGraph (Fin n)} (θ : σ ↪g Γ)
    (Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))) (M : ℕ) :
    (1 : ℚ) / (n ^ n₀) ≤ flagDensity₁ σ.toEmptyTypeFlag (blowupFlagSeq_sub Γ Wf M).2 := by
  rw [blowupFlagSeq_sub_snd, flagDensity_type_eq_subgraphDensity]
  exact subgraphDensity_subBlowupGraphFin_lower hn θ Wf M

theorem blowup_limit_type_pos_sub {n : ℕ} (hn : 0 < n) {σ : FlagType (Fin n₀)}
    {Γ : SimpleGraph (Fin n)} (θ : σ ↪g Γ)
    {Wf : (M : ℕ) → ∀ _v : Fin n, SimpleGraph (Fin (M + 1))} {ϕ : ℕ → ℕ} {φ₀ : PositiveHom ∅ₜ}
    (hconv : ConvergesTo (blowupFlagSeq_sub Γ Wf ∘ ϕ) φ₀.coe) :
    φ₀ ⟨σ⟩₀ > 0 := by
  have hval : φ₀ ⟨σ⟩₀ = φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩ := by
    show φ₀ ⟦basisVector ⟨n₀, σ.toEmptyTypeFlag⟩⟧ = φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩
    rw [φ₀.coe_flag]
  rw [hval]
  set F₀ : FinFlag ∅ₜ := ⟨n₀, σ.toEmptyTypeFlag⟩ with hF₀
  have hlim : Tendsto (fun M => flagDensitySeq (blowupFlagSeq_sub Γ Wf ∘ ϕ) M F₀) atTop
      (𝓝 (φ₀.coe F₀)) := (flagSeq_convergesTo_iff.mp hconv).2 F₀
  set d₀ : ℝ := (1 : ℝ) / (n ^ n₀) with hd₀
  have hd₀pos : 0 < d₀ := by rw [hd₀]; positivity
  have hge : d₀ ≤ φ₀.coe F₀ := by
    refine ge_of_tendsto' hlim ?_
    intro M
    show d₀ ≤ (flagDensity₁ σ.toEmptyTypeFlag (blowupFlagSeq_sub Γ Wf (ϕ M)).2 : ℝ)
    have h := flagDensity_type_blowupFlagSeq_sub_lower hn θ Wf (ϕ M)
    rw [hd₀]
    have : ((1 : ℚ) / (n ^ n₀) : ℝ)
        ≤ (flagDensity₁ σ.toEmptyTypeFlag (blowupFlagSeq_sub Γ Wf (ϕ M)).2 : ℝ) := by
      exact_mod_cast h
    simpa using this
  linarith

end FlagAlgebras.MetaTheory
