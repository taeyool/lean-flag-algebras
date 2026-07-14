import LeanFlagAlgebras.MetaTheory.GraphClassConstraint
import LeanFlagAlgebras.MetaTheory.SupportClosure
import LeanFlagAlgebras.FlagAlgebra.RandomHom
import LeanFlagAlgebras.Forbid.TuranDensity

/-! # The uniform blow-up flag sequence and its base limit (paper §5, capstone part 2)

Fix a `GraphClass gc`, a type `σ`, and an **in-class base graph** `Γ` with `gc.Mem Γ` into
which `σ` embeds (`hemb : Nonempty (σ ↪g Γ)`).  This file packages the uniform-blow-up flag
sequence of `Γ` and extracts a base limit `φ₀` of it, establishing the two facts the
clone-root-plantability capstone needs from the base side:

* `blowupFlagSeq` — the `FlagSeq ∅ₜ` whose `M`-th flag is the unlabelled uniform
  `(M+1)`-blow-up of `Γ`, presented on `Fin (n·(M+1))` via the canonical equivalence
  `(Σ v : Fin n, Fin (M+1)) ≃ Fin (n·(M+1))` and shown to have strictly increasing sizes
  (`blowupFlagSeq_increases`).  Each flag is **in the class** (`blowupGraphFin_mem`, via
  `gc.clone_closed` and heredity along the presentation iso).

* `exists_blowup_limit` — a subsequence of `blowupFlagSeq` converges (compactness of the
  density-profile space) to the density profile `φ₀.coe` of a base positive homomorphism
  `φ₀ : PositiveHom ∅ₜ`.

* `blowup_limit_mem_Q0` — `posHomPoint φ₀ ∈ Qσ (constraintOf gc σ).forb0`.  Because every
  blow-up is in the class, every forbidden graph has density `0` in it
  (`forbiddenFree_of_mem`), so the limit kills every forbidden flag, and `mem_Qσ_iff`
  concludes.

* `blowup_limit_type_pos` — `φ₀ ⟨σ⟩₀ > 0`.  Here we prove a **uniform positive lower bound**
  on the σ-type density across the whole sequence:
  `flagDensity₁ σ.toEmptyTypeFlag (blowupFlagSeq Γ M) ≥ 1 / n^n₀` for every `M`.  The bound
  comes from a direct subset count: a fixed embedding `θ : σ ↪g Γ` gives, for each clone
  choice `c : Fin n₀ → Fin (M+1)`, the *planted* vertex set `{⟨θ i, c i⟩ : i}` of the
  `(M+1)`-blow-up, which induces a copy of `σ`; distinct choices give distinct induced
  subgraphs, so `subgraphCount σ (blow-up) ≥ (M+1)^{n₀}`, while the number of all `n₀`-subsets
  is `≤ (n(M+1))^{n₀} = n^{n₀}(M+1)^{n₀}`.  Passing to the limit, `φ₀ ⟨σ⟩₀ ≥ 1/n^{n₀} > 0`.

The capstone consumes these as: "from an in-class base with a σ-copy, get `φ₀ ∈ Q₀` with
`φ₀⟨σ⟩₀ > 0`, as a subsequential blow-up limit."
-/

open Filter Topology
open SimpleGraph Finset GraphAlgebras

namespace FlagAlgebras.MetaTheory

open FlagAlgebras Forbid

attribute [local instance] Classical.propDecidable

variable {n₀ : ℕ}

/-! ## The uniform blow-up, presented on `Fin (n·(M+1))` -/

/-- The canonical equivalence `(Σ v : Fin n, Fin (M+1)) ≃ Fin (n·(M+1))`, used to present the
host of the uniform `(M+1)`-blow-up as a `Fin`-type. -/
noncomputable def blowupHostEquiv (n M : ℕ) :
    (Σ _v : Fin n, Fin (M + 1)) ≃ Fin (n * (M + 1)) := by
  have e : (Σ _v : Fin n, Fin (M + 1)) ≃ Fin (∑ _i : Fin n, (M + 1)) := finSigmaFinEquiv
  have hsum : (∑ _i : Fin n, (M + 1)) = n * (M + 1) := by
    simp [Finset.sum_const, Finset.card_univ]
  exact e.trans (finCongr hsum)

/-- The uniform `(M+1)`-blow-up of `Γ`, presented as a simple graph on `Fin (n·(M+1))` by
transporting along `blowupHostEquiv`. -/
noncomputable def blowupGraphFin {n : ℕ} (Γ : SimpleGraph (Fin n)) (M : ℕ) :
    SimpleGraph (Fin (n * (M + 1))) :=
  SimpleGraph.map (blowupHostEquiv n M).toEmbedding (independentBlowup Γ (fun _ => M + 1))

/-- The presentation iso: the `Σ`-hosted blow-up is isomorphic to its `Fin`-hosted
presentation `blowupGraphFin`. -/
noncomputable def blowupGraphFin_iso {n : ℕ} (Γ : SimpleGraph (Fin n)) (M : ℕ) :
    independentBlowup Γ (fun _ => M + 1) ≃g blowupGraphFin Γ M :=
  SimpleGraph.Iso.map (blowupHostEquiv n M) (independentBlowup Γ (fun _ => M + 1))

/-- **Each blow-up presentation is in the class.**  Independent blow-ups of an in-class graph
are in the class (`gc.clone_closed`); membership transports along the presentation iso by
heredity. -/
theorem blowupGraphFin_mem (gc : GraphClass) {n : ℕ} {Γ : SimpleGraph (Fin n)}
    (hΓ : gc.Mem Γ) (M : ℕ) : gc.Mem (blowupGraphFin Γ M) := by
  have hblow : gc.Mem (independentBlowup Γ (fun _ => M + 1)) :=
    gc.clone_closed Γ (fun _ => M + 1) hΓ
  exact gc.comap (blowupGraphFin_iso Γ M).symm.toEmbedding hblow

/-! ## The flag sequence -/

/-- The unlabelled `M`-th flag: the uniform `(M+1)`-blow-up of `Γ` as an `∅ₜ`-flag on
`Fin (n·(M+1))`. -/
noncomputable def blowupFlagSeq {n : ℕ} (Γ : SimpleGraph (Fin n)) : FlagSeq ∅ₜ :=
  fun M => ⟨n * (M + 1), graphFlag (blowupGraphFin Γ M)⟩

/-- The size of the `M`-th blow-up flag is `n·(M+1)`. -/
@[simp]
theorem blowupFlagSeq_fst {n : ℕ} (Γ : SimpleGraph (Fin n)) (M : ℕ) :
    (blowupFlagSeq Γ M).1 = n * (M + 1) := rfl

/-- The underlying flag of the `M`-th blow-up flag is the graph flag of `blowupGraphFin Γ M`. -/
@[simp]
theorem blowupFlagSeq_snd {n : ℕ} (Γ : SimpleGraph (Fin n)) (M : ℕ) :
    (blowupFlagSeq Γ M).2 = graphFlag (blowupGraphFin Γ M) := rfl

/-- **The blow-up flag sizes strictly increase**: `n·(M+1)` is strictly monotone in `M` once
`Γ` is nonempty (`0 < n`). -/
theorem blowupFlagSeq_increases {n : ℕ} (hn : 0 < n) (Γ : SimpleGraph (Fin n)) :
    Increases (blowupFlagSeq Γ) := by
  apply increases_of_consecutive_lt
  intro M
  simp only [blowupFlagSeq_fst]
  gcongr
  omega

/-! ## The base limit -/

/-- **A convergent subsequence of the blow-up flag sequence.**  The sizes strictly increase,
so by compactness of the density-profile space there is a strictly monotone reindexing `ϕ`
and a base positive homomorphism `φ₀` whose density profile is the limit. -/
theorem exists_blowup_limit {n : ℕ} (hn : 0 < n) (Γ : SimpleGraph (Fin n)) :
    ∃ (ϕ : ℕ → ℕ) (φ₀ : PositiveHom ∅ₜ),
      StrictMono ϕ ∧ ConvergesTo (blowupFlagSeq Γ ∘ ϕ) φ₀.coe := by
  obtain ⟨a, ϕ, hϕ, hconv⟩ :=
    increasing_flagSeq_contain_convergent_subseq (blowupFlagSeq Γ) (blowupFlagSeq_increases hn Γ)
  obtain ⟨φ₀, hφ₀⟩ := flagSeq_limit_mem_positiveHom (blowupFlagSeq Γ ∘ ϕ) hconv
  exact ⟨ϕ, φ₀, hϕ, hφ₀ ▸ hconv⟩

/-! ## Part 3: the base limit lies in `Q₀` -/

/-- The density of every forbidden graph is `0` in every blow-up flag (each blow-up is in the
class, so it is forbidden-free by `forbiddenFree_of_mem`). -/
theorem flagDensity_forbidden_blowupFlagSeq_zero (gc : GraphClass) {n₀ : ℕ}
    {σ : FlagType (Fin n₀)} {n : ℕ} {Γ : SimpleGraph (Fin n)} (hΓ : gc.Mem Γ) (M : ℕ)
    {D : FinFlag ∅ₜ} (hD : (constraintOf gc σ).forb0 D) :
    flagDensity₁ D.2 (blowupFlagSeq Γ M).2 = 0 := by
  simpa only [blowupFlagSeq_snd] using
    forbiddenFree_of_mem gc (blowupGraphFin Γ M) (blowupGraphFin_mem gc hΓ M) D hD

/-- **The base limit lies in `Q₀`.**  Since every blow-up is forbidden-free, the limit `φ₀`
assigns density `0` to every forbidden graph, so `posHomPoint φ₀ ∈ Qσ (constraintOf gc σ).forb0`
by the intrinsic description of `Q₀`. -/
theorem blowup_limit_mem_Q0 (gc : GraphClass) {n₀ : ℕ} {σ : FlagType (Fin n₀)} {n : ℕ}
    {Γ : SimpleGraph (Fin n)} (hΓ : gc.Mem Γ) {ϕ : ℕ → ℕ} {φ₀ : PositiveHom ∅ₜ}
    (hconv : ConvergesTo (blowupFlagSeq Γ ∘ ϕ) φ₀.coe) :
    posHomPoint φ₀ ∈ Qσ (constraintOf gc σ).forb0 := by
  rw [mem_Qσ_iff]
  intro D hD
  -- `(posHomPoint φ₀).val D = φ₀.coe D`, the limit of the densities of `D` in the blow-ups.
  rw [posHomPoint_val_apply, ← φ₀.coe_flag D]
  have hlim : Tendsto (fun M => flagDensitySeq (blowupFlagSeq Γ ∘ ϕ) M D) atTop (𝓝 (φ₀.coe D)) :=
    (flagSeq_convergesTo_iff.mp hconv).2 D
  have hzero : ∀ M, flagDensitySeq (blowupFlagSeq Γ ∘ ϕ) M D = 0 := by
    intro M
    show (flagDensity₁ D.2 (blowupFlagSeq Γ (ϕ M)).2 : ℝ) = 0
    rw [flagDensity_forbidden_blowupFlagSeq_zero gc hΓ (ϕ M) hD, Rat.cast_zero]
  rw [tendsto_congr hzero, tendsto_const_nhds_iff] at hlim
  exact hlim.symm

/-! ## Part 4: a uniform positive lower bound on the σ-type density

The σ-type graph is an induced subgraph of every blow-up, with a *uniform* positive lower
bound on its density, obtained by a direct planted-subset count. -/

/-- `n₀ ≤ n` whenever `σ` (on `Fin n₀`) embeds into `Γ` (on `Fin n`). -/
theorem fin_card_le_of_embedding {n : ℕ} {σ : FlagType (Fin n₀)} {Γ : SimpleGraph (Fin n)}
    (θ : σ ↪g Γ) : n₀ ≤ n := by
  have := Fintype.card_le_of_injective θ θ.injective
  simpa using this

/-- The *planted* vertex set of the `(M+1)`-blow-up of `Γ` for a clone choice
`c : Fin n₀ → Fin (M+1)`: place each labelled vertex `i` at the clone `⟨θ i, c i⟩`. -/
noncomputable def plantedSet {n : ℕ} {σ : FlagType (Fin n₀)} {Γ : SimpleGraph (Fin n)}
    (θ : σ ↪g Γ) (M : ℕ) (c : Fin n₀ → Fin (M + 1)) :
    Finset (Σ _v : Fin n, Fin (M + 1)) :=
  Finset.univ.image (fun i : Fin n₀ => (⟨θ i, c i⟩ : Σ _v : Fin n, Fin (M + 1)))

/-- The induced subgraph on a planted set is a copy of `σ`: the labelling
`i ↦ ⟨θ i, c i⟩` is a graph isomorphism `σ ≃g` (induced subgraph), because two clones are
adjacent in the blow-up iff their base vertices are `Γ`-adjacent, which is `σ`-adjacency by
`θ`. -/
noncomputable def plantedIso {n : ℕ} {σ : FlagType (Fin n₀)} {Γ : SimpleGraph (Fin n)}
    (θ : σ ↪g Γ) (M : ℕ) (c : Fin n₀ → Fin (M + 1)) :
    σ ≃g ((⊤ : (independentBlowup Γ (fun _ => M + 1)).Subgraph).induce
        (↑(plantedSet θ M c) : Set _)).coe := by
  set B := independentBlowup Γ (fun _ => M + 1)
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
  simp only [Subgraph.induce_adj, Subgraph.top_adj]
  constructor
  · rintro ⟨_, _, hadj⟩
    exact θ.map_adj_iff.mp hadj
  · intro h
    exact ⟨(f i).2, (f j).2, θ.map_adj_iff.mpr h⟩

/-- **Planted lower bound on the σ-count.**  There are at least `(M+1)^{n₀}` induced copies of
`σ` in the `(M+1)`-blow-up of `Γ`: distinct clone choices `c` give distinct planted induced
subgraphs (they have distinct vertex sets). -/
theorem pow_le_subgraphCount_independentBlowup {n : ℕ} {σ : FlagType (Fin n₀)}
    {Γ : SimpleGraph (Fin n)} (θ : σ ↪g Γ) (M : ℕ) :
    (M + 1) ^ n₀ ≤ subgraphCount σ (independentBlowup Γ (fun _ => M + 1)) := by
  set B := independentBlowup Γ (fun _ => M + 1)
  -- The planted induced subgraphs all lie in `subgraphSet σ B`.
  have hmaps : ∀ c : Fin n₀ → Fin (M + 1),
      (⊤ : B.Subgraph).induce (↑(plantedSet θ M c) : Set _) ∈ subgraphSet σ B := by
    intro c
    rw [mem_subgraphSet_iff]
    exact ⟨Subgraph.induce_top_isInduced _ _, ⟨(plantedIso θ M c).symm⟩⟩
  -- Distinct clone choices give distinct planted subgraphs.
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

/-- The σ-count in the `Fin`-presented blow-up matches that of the `Σ`-hosted blow-up (iso). -/
theorem subgraphCount_blowupGraphFin {n : ℕ} (σ : FlagType (Fin n₀)) (Γ : SimpleGraph (Fin n))
    (M : ℕ) :
    subgraphCount σ (blowupGraphFin Γ M)
      = subgraphCount σ (independentBlowup Γ (fun _ => M + 1)) :=
  (subgraphCount_eq_of_iso σ (blowupGraphFin_iso Γ M)).symm

/-- **Uniform positive lower bound on the σ-type density.**  For every `M`, the density of the
σ-type graph in the `(M+1)`-blow-up presentation is at least `1 / n^{n₀}` (a constant
independent of `M`).  Uses the planted count `≥ (M+1)^{n₀}` and `N.choose n₀ ≤ N^{n₀}`. -/
theorem subgraphDensity_blowupGraphFin_lower {n : ℕ} (hn : 0 < n) {σ : FlagType (Fin n₀)}
    {Γ : SimpleGraph (Fin n)} (θ : σ ↪g Γ) (M : ℕ) :
    (1 : ℚ) / (n ^ n₀) ≤ subgraphDensity σ (blowupGraphFin Γ M) := by
  have hn0 : n₀ ≤ n := fin_card_le_of_embedding θ
  -- The count is `≥ (M+1)^{n₀}`.
  have hcnt : (M + 1) ^ n₀ ≤ subgraphCount σ (blowupGraphFin Γ M) := by
    rw [subgraphCount_blowupGraphFin]
    exact pow_le_subgraphCount_independentBlowup θ M
  -- The vertex count of the presented blow-up is `n·(M+1)`.
  have hcardV : Fintype.card (Fin n₀) = n₀ := Fintype.card_fin n₀
  have hcardW : Fintype.card (Fin (n * (M + 1))) = n * (M + 1) := Fintype.card_fin _
  -- Unfold the density and run the arithmetic.
  set cnt := subgraphCount σ (blowupGraphFin Γ M) with hcntdef
  have hdens : subgraphDensity σ (blowupGraphFin Γ M)
      = (cnt : ℚ) / ((n * (M + 1)).choose n₀) := by
    simp only [subgraphDensity, hcardV, hcardW, hcntdef]
  rw [hdens]
  -- Pure arithmetic: cnt ≥ (M+1)^{n₀}, choose ≤ N^{n₀} = n^{n₀}(M+1)^{n₀}, so density ≥ 1/n^{n₀}.
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

/-! ## Part 4 conclusion: the σ-type gets positive mass at the limit -/

/-- The bridge `flagDensity₁ σ.toEmptyTypeFlag (graphFlag B) = subgraphDensity σ B`: the
σ-type density of an `∅ₜ`-flag is the underlying induced-subgraph density. -/
theorem flagDensity_type_eq_subgraphDensity {N : ℕ} (σ : FlagType (Fin n₀))
    (B : SimpleGraph (Fin N)) :
    flagDensity₁ σ.toEmptyTypeFlag (graphFlag B) = subgraphDensity σ B := by
  rw [subgraphDensity_eq_flagDensity₁]; rfl

/-- **Uniform positive lower bound on the σ-type density of the blow-up flags.**  Combines the
density bound with the flag/subgraph bridge. -/
theorem flagDensity_type_blowupFlagSeq_lower {n : ℕ} (hn : 0 < n) {σ : FlagType (Fin n₀)}
    {Γ : SimpleGraph (Fin n)} (θ : σ ↪g Γ) (M : ℕ) :
    (1 : ℚ) / (n ^ n₀) ≤ flagDensity₁ σ.toEmptyTypeFlag (blowupFlagSeq Γ M).2 := by
  rw [blowupFlagSeq_snd, flagDensity_type_eq_subgraphDensity]
  exact subgraphDensity_blowupGraphFin_lower hn θ M

/-- **The base limit gives the σ-type positive mass.**  `φ₀ ⟨σ⟩₀` is the limit of the σ-type
densities along the blow-up sequence, each `≥ 1/n^{n₀}`, so the limit is `≥ 1/n^{n₀} > 0`. -/
theorem blowup_limit_type_pos {n : ℕ} (hn : 0 < n) {σ : FlagType (Fin n₀)}
    {Γ : SimpleGraph (Fin n)} (θ : σ ↪g Γ) {ϕ : ℕ → ℕ} {φ₀ : PositiveHom ∅ₜ}
    (hconv : ConvergesTo (blowupFlagSeq Γ ∘ ϕ) φ₀.coe) :
    φ₀ ⟨σ⟩₀ > 0 := by
  -- `φ₀ ⟨σ⟩₀ = φ₀.coe (σ-as-∅ₜ-flag)`, the limit of the σ-type densities along the blow-ups.
  have hval : φ₀ ⟨σ⟩₀ = φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩ := by
    show φ₀ ⟦basisVector ⟨n₀, σ.toEmptyTypeFlag⟩⟧ = φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩
    rw [φ₀.coe_flag]
  rw [hval]
  set F₀ : FinFlag ∅ₜ := ⟨n₀, σ.toEmptyTypeFlag⟩ with hF₀
  have hlim : Tendsto (fun M => flagDensitySeq (blowupFlagSeq Γ ∘ ϕ) M F₀) atTop
      (𝓝 (φ₀.coe F₀)) := (flagSeq_convergesTo_iff.mp hconv).2 F₀
  -- The limit is `≥ 1/n^{n₀}` since every term is.
  set d₀ : ℝ := (1 : ℝ) / (n ^ n₀) with hd₀
  have hd₀pos : 0 < d₀ := by rw [hd₀]; positivity
  have hge : d₀ ≤ φ₀.coe F₀ := by
    refine ge_of_tendsto' hlim ?_
    intro M
    show d₀ ≤ (flagDensity₁ σ.toEmptyTypeFlag (blowupFlagSeq Γ (ϕ M)).2 : ℝ)
    have h := flagDensity_type_blowupFlagSeq_lower hn θ (ϕ M)
    rw [hd₀]
    have : ((1 : ℚ) / (n ^ n₀) : ℝ) ≤ (flagDensity₁ σ.toEmptyTypeFlag (blowupFlagSeq Γ (ϕ M)).2 : ℝ) := by
      exact_mod_cast h
    simpa using this
  linarith

end FlagAlgebras.MetaTheory
