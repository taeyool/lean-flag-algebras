import LeanFlagAlgebras.MetaTheory.HeredClass
import LeanFlagAlgebras.MetaTheory.ConstrainedRep
import LeanFlagAlgebras.MetaTheory.CapstoneShared
import LeanFlagAlgebras.MetaTheory.WeakConvergence
import LeanFlagAlgebras.MetaTheory.BlowupSequence
import LeanFlagAlgebras.MetaTheory.SupportClosure

/-! # Finite planting implies root-plantability (paper §8)

This is the Lean counterpart of paper §8's first abstract criterion: `def:finite-local-planting`
and `thm:finite-local-planting`.

A hereditary class `K` has the **finite planting property at `σ`** (`FinitePlanting`) if, for every
resolution `m ≥ k = |σ|` and tolerance `ε > 0`, there are a threshold `n₁` and a density `δ > 0`
such that every sufficiently large in-class `σ`-flag `(G, θ)` can be replaced by a larger in-class
graph `H` together with a positive-density set `Θ` of `σ`-embeddings into `H` whose `σ`-flag
densities (on flags of size `≤ m`) all match those of `(G, θ)` up to `ε`.

`finitePlanting_root_plantable` (`thm:finite-local-planting`): the finite planting property at a
non-degenerate type `σ` implies root-plantability, `S_σ = Q_σ`.

The proof mirrors the §5 capstone `clone_root_plantable`, but with the uniform blow-up sequence of a
*single* base graph replaced by the abstract planting family `Hₜ` — one planting per term of the
constrained representation sequence.  Everything construction-agnostic is reused verbatim from
[`CapstoneShared`](./CapstoneShared.lean) (the cylinder-closure criterion, the closed cylinders, and
the rooting-measure-as-labelling-count identity), [`WeakConvergence`](./WeakConvergence.lean) (weak
convergence of the rooting measures of *any* convergent flag sequence), and
[`SupportClosure`](./SupportClosure.lean) (the support/Portmanteau tail).
-/

open MeasureTheory Filter Topology
open SimpleGraph
open scoped GraphAlgebras

namespace FlagAlgebras.MetaTheory

open FlagAlgebras GraphAlgebras

attribute [local instance] Classical.propDecidable

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## The finite planting property -/

/-- **Finite planting property** (`def:finite-local-planting`).  The hereditary class `hc` has the
finite planting property at the type `σ` (with `k = n₀` labelled vertices) if: for every `m ≥ n₀`
and every `ε > 0`, there are `n₁ ≥ m` and `δ > 0` such that every `σ`-flag `(G, θ)` (presented as a
`LabeledGraph σ (Fin n)`) with `G ∈ hc` and `n ≥ n₁` admits a graph `H ∈ hc` and a finite set `Θ` of
`σ`-embeddings `σ ↪g H` with

* `n ≤ N` (where `N = |V(H)|`)  — clause (i);
* `δ · N^{n₀} ≤ |Θ|`            — clause (ii);
* `|p(F, (H, θ')) − p(F, (G, θ))| < ε` for every `θ' ∈ Θ` and every `σ`-flag `F` with `|F| ≤ m`
  — clause (iii). -/
def FinitePlanting (hc : HeredClass) (σ : FlagType (Fin n₀)) : Prop :=
  ∀ (m : ℕ) (ε : ℝ), n₀ ≤ m → 0 < ε →
    ∃ (n₁ : ℕ) (δ : ℝ), m ≤ n₁ ∧ 0 < δ ∧
      ∀ (n : ℕ) (G : LabeledGraph σ (Fin n)), hc.Mem G.graph → n₁ ≤ n →
        ∃ (N : ℕ) (H : SimpleGraph (Fin N)) (Θ : Finset (σ ↪g H)),
          hc.Mem H ∧ n ≤ N ∧
          (δ * (N : ℝ) ^ n₀ ≤ (Θ.card : ℝ)) ∧
          ∀ θ' ∈ Θ, ∀ F : FinFlag σ, F.1 ≤ m →
            |(flagDensity₁ F.2 (⟦(⟨H, θ'⟩ : LabeledGraph σ (Fin N))⟧ : Flag σ (Fin N)) : ℝ)
                - (flagDensity₁ F.2 (⟦G⟧ : Flag σ (Fin n)) : ℝ)| < ε

/-! ## Counting: σ-embeddings, induced σ-subgraphs and the σ-type density bound -/

/-- The graph isomorphism `σ ≃g (subgraph induced on the range of a `σ`-embedding)`: a `σ`-embedding
`e : σ ↪g G` is an isomorphism onto the subgraph of `G` induced on its image. -/
private noncomputable def embeddingImageIso {N : ℕ} {σ : FlagType (Fin n₀)} {G : SimpleGraph (Fin N)}
    (e : σ ↪g G) : σ ≃g ((⊤ : G.Subgraph).induce (Set.range (e : Fin n₀ → Fin N))).coe := by
  set S : Set (Fin N) := Set.range (e : Fin n₀ → Fin N) with hS
  have hmem : ∀ i : Fin n₀, (e i) ∈ S := fun i => ⟨i, rfl⟩
  let f : Fin n₀ → {x // x ∈ ((⊤ : G.Subgraph).induce S).verts} :=
    fun i => ⟨e i, by rw [Subgraph.induce_verts]; exact hmem i⟩
  have hf_inj : Function.Injective f := fun i j h => e.injective (Subtype.ext_iff.mp h)
  have hf_surj : Function.Surjective f := by
    rintro ⟨x, hx⟩; rw [Subgraph.induce_verts] at hx
    obtain ⟨i, hi⟩ := hx; exact ⟨i, Subtype.ext hi⟩
  refine ⟨Equiv.ofBijective f ⟨hf_inj, hf_surj⟩, ?_⟩
  intro i j; simp only [Equiv.ofBijective_apply, Subgraph.coe_adj]
  constructor
  · rintro ⟨_, _, hadj⟩; exact e.map_adj_iff.mp hadj
  · intro h; exact ⟨hmem i, hmem j, e.map_adj_iff.mpr h⟩

/-- The fiber bound: at most `n₀!` σ-embeddings of `σ` into `G` induce the same subgraph (i.e. have
the same image vertex set), because two such embeddings differ by a permutation of `Fin n₀`. -/
private theorem fiber_card_le {N : ℕ} {σ : FlagType (Fin n₀)} {G : SimpleGraph (Fin N)}
    (g : G.Subgraph) :
    (Finset.univ.filter (fun e : σ ↪g G =>
      (⊤ : G.Subgraph).induce (Set.range (e : Fin n₀ → Fin N)) = g)).card ≤ Nat.factorial n₀ := by
  classical
  set fib := Finset.univ.filter (fun e : σ ↪g G =>
      (⊤ : G.Subgraph).induce (Set.range (e : Fin n₀ → Fin N)) = g) with hfib
  rcases fib.eq_empty_or_nonempty with hemp | ⟨e₀, he₀⟩
  · rw [hemp]; simp
  · have hrange : ∀ e ∈ fib, Set.range (e : Fin n₀ → Fin N) = Set.range (e₀ : Fin n₀ → Fin N) := by
      intro e he
      rw [hfib, Finset.mem_filter] at he he₀
      have : (⊤ : G.Subgraph).induce (Set.range (e : Fin n₀ → Fin N))
           = (⊤ : G.Subgraph).induce (Set.range (e₀ : Fin n₀ → Fin N)) := by rw [he.2, he₀.2]
      have h2 := congrArg Subgraph.verts this
      rwa [Subgraph.induce_verts, Subgraph.induce_verts] at h2
    have hmem : ∀ e ∈ fib, ∀ i : Fin n₀, e i ∈ Set.range (e₀ : Fin n₀ → Fin N) := by
      intro e he i; rw [← hrange e he]; exact ⟨i, rfl⟩
    let pe : (e : σ ↪g G) → (he : e ∈ fib) → (Fin n₀ → Fin n₀) :=
      fun e he i => e₀.injective.invOfMemRange ⟨e i, hmem e he i⟩
    have hpe_spec : ∀ e (he : e ∈ fib) (i : Fin n₀), (e₀ : Fin n₀ → Fin N) (pe e he i) = e i :=
      fun e he i => e₀.injective.left_inv_of_invOfMemRange ⟨e i, hmem e he i⟩
    have hpe_inj : ∀ e (he : e ∈ fib), Function.Injective (pe e he) := by
      intro e he i j hij; apply e.injective
      rw [← hpe_spec e he i, ← hpe_spec e he j, hij]
    have key : fib.card ≤ Fintype.card (Equiv.Perm (Fin n₀)) := by
      apply Finset.card_le_card_of_injOn
        (f := fun e => if he : e ∈ fib then
          Equiv.ofBijective (pe e he)
            ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hpe_inj e he, rfl⟩)
          else 1)
        (fun a _ => Finset.mem_univ _)
      intro a ha' b hb' hab
      have ha : a ∈ fib := Finset.mem_coe.mp ha'
      have hb : b ∈ fib := Finset.mem_coe.mp hb'
      simp only at hab
      rw [dif_pos ha, dif_pos hb] at hab
      have hpe_eq : pe a ha = pe b hb := by
        funext i
        have := congrArg (fun (p : Equiv.Perm (Fin n₀)) => p i) hab
        simpa only [Equiv.ofBijective_apply] using this
      ext i; rw [← hpe_spec a ha i, ← hpe_spec b hb i, hpe_eq]
    rw [Fintype.card_perm, Fintype.card_fin] at key
    exact key

/-- **Counting:** the number of σ-embeddings into `G` is at most `n₀!` times the number of induced
copies of `σ` (each induced copy of `σ` carries at most `n₀!` embeddings). -/
private theorem card_embeddings_le_subgraphCount {N : ℕ} (σ : FlagType (Fin n₀))
    (G : SimpleGraph (Fin N)) :
    Fintype.card (σ ↪g G) ≤ subgraphCount σ G * Nat.factorial n₀ := by
  classical
  have hmaps : ∀ e ∈ (Finset.univ : Finset (σ ↪g G)),
      (⊤ : G.Subgraph).induce (Set.range (e : Fin n₀ → Fin N)) ∈ subgraphSet σ G := by
    intro e _
    rw [mem_subgraphSet_iff]
    exact ⟨Subgraph.induce_top_isInduced _ _, ⟨(embeddingImageIso e).symm⟩⟩
  have hfiber : ∀ b ∈ subgraphSet σ G,
      (Finset.univ.filter (fun e : σ ↪g G =>
        (⊤ : G.Subgraph).induce (Set.range (e : Fin n₀ → Fin N)) = b)).card ≤ Nat.factorial n₀ :=
    fun b _ => fiber_card_le b
  have := Finset.card_le_mul_card_image_of_maps_to hmaps (Nat.factorial n₀) hfiber
  rw [Finset.card_univ, mul_comm] at this
  exact le_trans this (le_of_eq (by rw [subgraphCount]))

/-- **σ-type density lower bound from a planting.**  If `Θ` is a finite set of `σ`-embeddings into
`G` with `δ · N^{n₀} ≤ |Θ|`, then the σ-subgraph density of `G` is at least `δ / n₀!`. -/
private theorem subgraphDensity_lower_of_planting {N : ℕ} {σ : FlagType (Fin n₀)}
    {G : SimpleGraph (Fin N)} (Θ : Finset (σ ↪g G)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ * (N : ℝ) ^ n₀ ≤ (Θ.card : ℝ)) (hn₀N : n₀ ≤ N) :
    (δ / Nat.factorial n₀ : ℝ) ≤ (subgraphDensity σ G : ℝ) := by
  classical
  have hΘ_le : (Θ.card : ℝ) ≤ (subgraphCount σ G : ℝ) * (Nat.factorial n₀ : ℝ) := by
    have h1 : Θ.card ≤ Fintype.card (σ ↪g G) := by
      rw [← Finset.card_univ]; exact Finset.card_le_univ Θ
    have h2 := card_embeddings_le_subgraphCount σ G
    calc (Θ.card : ℝ) ≤ (Fintype.card (σ ↪g G) : ℝ) := by exact_mod_cast h1
      _ ≤ (subgraphCount σ G * Nat.factorial n₀ : ℕ) := by exact_mod_cast h2
      _ = (subgraphCount σ G : ℝ) * (Nat.factorial n₀ : ℝ) := by push_cast; ring
  have hdens : (subgraphDensity σ G : ℝ) = (subgraphCount σ G : ℝ) / ((N.choose n₀ : ℕ) : ℝ) := by
    simp only [subgraphDensity, Fintype.card_fin]; push_cast; rfl
  rw [hdens]
  have hchoose_pos : 0 < N.choose n₀ := Nat.choose_pos hn₀N
  have hchoose_le : (N.choose n₀ : ℝ) ≤ (N : ℝ) ^ n₀ := by exact_mod_cast Nat.choose_le_pow N n₀
  have hfact_pos : (0 : ℝ) < (Nat.factorial n₀ : ℝ) := by exact_mod_cast Nat.factorial_pos n₀
  have hchoose_posR : (0 : ℝ) < (N.choose n₀ : ℝ) := by exact_mod_cast hchoose_pos
  rw [div_le_div_iff₀ hfact_pos hchoose_posR]
  calc δ * (N.choose n₀ : ℝ)
      ≤ δ * (N : ℝ) ^ n₀ := mul_le_mul_of_nonneg_left hchoose_le hδ0
    _ ≤ (Θ.card : ℝ) := hδ
    _ ≤ (subgraphCount σ G : ℝ) * (Nat.factorial n₀ : ℝ) := hΘ_le

/-- The σ-type density of `graphFlag G` is at least `δ / n₀!` given a planting `Θ`. -/
private theorem flagDensity_type_lower_of_planting {N : ℕ} {σ : FlagType (Fin n₀)}
    {G : SimpleGraph (Fin N)} (Θ : Finset (σ ↪g G)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ * (N : ℝ) ^ n₀ ≤ (Θ.card : ℝ)) (hn₀N : n₀ ≤ N) :
    (δ / Nat.factorial n₀ : ℝ)
      ≤ (flagDensity₁ σ.toEmptyTypeFlag (graphFlag G) : ℝ) := by
  rw [flagDensity_type_eq_subgraphDensity]
  exact subgraphDensity_lower_of_planting Θ hδ0 hδ hn₀N

/-! ## Bundled planting data -/

/-- The bundled output of one planting: a host graph `H`, a finite set `Θ` of `σ`-embeddings into
it, and the three planting clauses. -/
private structure PlantData (hc : HeredClass) (σ : FlagType (Fin n₀)) (δ tol : ℝ) (m : ℕ)
    {n : ℕ} (G : LabeledGraph σ (Fin n)) where
  N : ℕ
  H : SimpleGraph (Fin N)
  Θ : Finset (σ ↪g H)
  memH : hc.Mem H
  size_le : n ≤ N
  card_lb : δ * (N : ℝ) ^ n₀ ≤ (Θ.card : ℝ)
  close : ∀ θ' ∈ Θ, ∀ F : FinFlag σ, F.1 ≤ m →
    |(flagDensity₁ F.2 (⟦(⟨H, θ'⟩ : LabeledGraph σ (Fin N))⟧ : Flag σ (Fin N)) : ℝ)
        - (flagDensity₁ F.2 (⟦G⟧ : Flag σ (Fin n)) : ℝ)| < tol

/-! ## The base limit lies in `Q₀` (generic version) -/

/-- **The base limit lies in `Q₀`** (generic form of `blowup_limit_mem_Q0`).  If every term of a
convergent flag sequence `sH` is forbidden-free (zero density of every forbidden graph), the limit
`φ₀` kills every forbidden flag, so `posHomPoint φ₀ ∈ Qσ T.forb0`. -/
private theorem flagSeqLimit_mem_Q0 {σ : FlagType (Fin n₀)} (T : Constraint σ)
    {sH : FlagSeq ∅ₜ} {φ₀ : PositiveHom ∅ₜ} (hconv : ConvergesTo sH φ₀.coe)
    (hff : ∀ k, ∀ D : FinFlag ∅ₜ, T.forb0 D → flagDensity₁ D.2 (sH k).2 = 0) :
    posHomPoint φ₀ ∈ Qσ T.forb0 := by
  rw [mem_Qσ_iff]
  intro D hD
  rw [posHomPoint_val_apply, ← φ₀.coe_flag D]
  have hlim : Tendsto (fun k => flagDensitySeq sH k D) atTop (𝓝 (φ₀.coe D)) :=
    (flagSeq_convergesTo_iff.mp hconv).2 D
  have hzero : ∀ k, flagDensitySeq sH k D = 0 := by
    intro k
    show (flagDensity₁ D.2 (sH k).2 : ℝ) = 0
    rw [hff k D hD, Rat.cast_zero]
  rw [tendsto_congr hzero, tendsto_const_nhds_iff] at hlim
  exact hlim.symm

/-! ## The theorem -/

/-- **Finite planting implies root-plantability** (`thm:finite-local-planting`).  If the hereditary
class `hc` has the finite planting property at a non-degenerate type `σ` (`0 < n₀`), then
`constraintOf hc σ` is root-plantable, `S_σ = Q_σ`. -/
theorem finitePlanting_root_plantable (hc : HeredClass) (σ : FlagType (Fin n₀))
    (hn₀ : 0 < n₀) (hfp : FinitePlanting hc σ) :
    RootPlantable (hc.constraintOf σ) := by
  refine Set.Subset.antisymm (Sσ_subset_Qσ _) ?_
  intro ψ hψQ
  rw [mem_Qσ_iff] at hψQ
  set ψh : PositiveHom σ := PositiveHomSpace.toPosHom ψ with hψh
  have hψh_coe : ∀ F : FinFlag σ, ψh.coe F = ψ.val F := by
    intro F
    rw [PositiveHom.coe_flag, PositiveHomSpace.toPosHom_basisVector]
  have hψh_forb : ∀ F : FinFlag σ, (hc.constraintOf σ).forbσ F → ψh.coe F = 0 := by
    intro F hF; rw [hψh_coe]; exact hψQ F hF
  -- Constrained representation: a forbidden-free flag sequence converging to `ψh`.
  obtain ⟨s, hconv_s, hff⟩ :=
    exists_constrained_flagSeq_limit ψh (hc.constraintOf σ).forbσ hψh_forb
  -- Reduce membership in the closure `S_σ` to the cylinder criterion.
  apply mem_closure_of_forall_finset_cylinder
  intro Fs ε hε
  -- The resolution `m` and tolerance `ε/3`.
  set m : ℕ := n₀ ⊔ (Fs.sup (fun Fi => Fi.1)) with hm
  have hmn₀ : n₀ ≤ m := le_sup_left
  have hmFs : ∀ Fi ∈ Fs, Fi.1 ≤ m := by
    intro Fi hFi
    exact le_trans (Finset.le_sup hFi) le_sup_right
  -- Apply the finite-planting property.
  obtain ⟨n₁, δ, hmn₁, hδpos, hplant⟩ := hfp m (ε / 3) hmn₀ (by positivity)
  -- The sizes `(s t).1` tend to `+∞`.
  have hsize_atTop : Tendsto (fun t => (s t).1) atTop atTop :=
    (flagSeq_convergesTo_iff.mp hconv_s).1.tendsto_atTop
  -- Step into the tail where the densities are close and the size is `≥ n₁`.
  -- Choose `K` so that for `t ≥ K`: `(s t).1 ≥ n₁` and densities on `Fs` are within `ε/3` of `ψ`.
  have hdens_ev : ∀ Fi ∈ Fs, ∀ᶠ t in atTop,
      |(flagDensity₁ Fi.2 (s t).2 : ℝ) - ψ.val Fi| < ε / 3 := by
    intro Fi _
    have hconv := (flagSeq_convergesTo_iff.mp hconv_s).2 Fi
    rw [hψh_coe Fi] at hconv
    have hmetric := (Metric.tendsto_atTop.mp hconv) (ε / 3) (by positivity)
    obtain ⟨Nd, hNd⟩ := hmetric
    filter_upwards [eventually_ge_atTop Nd] with t ht
    have := hNd t ht
    rwa [Real.dist_eq] at this
  have hsize_ge : ∀ᶠ t in atTop, n₁ ≤ (s t).1 := hsize_atTop.eventually_ge_atTop n₁
  have hcomb : ∀ᶠ t in atTop, n₁ ≤ (s t).1 ∧
      ∀ Fi ∈ Fs, |(flagDensity₁ Fi.2 (s t).2 : ℝ) - ψ.val Fi| < ε / 3 := by
    filter_upwards [hsize_ge, (eventually_all_finset Fs).mpr hdens_ev] with t h1 h2
    exact ⟨h1, h2⟩
  rw [eventually_atTop] at hcomb
  obtain ⟨K, hK⟩ := hcomb
  -- The tail index map `idx₀ k = K + k`; sizes `(s (idx₀ k)).1` strictly increase and are `≥ n₁`.
  set idx₀ : ℕ → ℕ := fun k => K + k with hidx₀
  have hidx₀_mono : StrictMono idx₀ := fun a b hab => by simp only [hidx₀]; omega
  have hidx₀_ge : ∀ k, K ≤ idx₀ k := fun k => Nat.le_add_right K k
  -- Planting data at each tail index (extracted with `Classical.choice`).
  have hplantdata_ne : ∀ k, Nonempty (PlantData hc σ δ (ε / 3) m (s (idx₀ k)).2.out) := by
    intro k
    have hKi := hK (idx₀ k) (hidx₀_ge k)
    -- The base graph is in the class (forbidden-free).
    have hmemΓ : hc.Mem ((s (idx₀ k)).2.out).graph := by
      apply hc.mem_of_forbiddenFree ((s (idx₀ k)).2.out)
      intro F hF
      rw [Quotient.out_eq]
      exact hff (idx₀ k) F hF
    obtain ⟨N, H, Θ, hmemH, hsize_le, hcard_lb, hclose⟩ :=
      hplant (s (idx₀ k)).1 ((s (idx₀ k)).2.out) hmemΓ hKi.1
    exact ⟨N, H, Θ, hmemH, hsize_le, hcard_lb, hclose⟩
  set hplantdata : ∀ k, PlantData hc σ δ (ε / 3) m (s (idx₀ k)).2.out :=
    fun k => Classical.choice (hplantdata_ne k) with hplantdata_def
  -- Extract the planting data as functions.
  set Nf : ℕ → ℕ := fun k => (hplantdata k).N with hNf
  set Hf : (k : ℕ) → SimpleGraph (Fin (Nf k)) := fun k => (hplantdata k).H with hHf
  -- The sizes `Nf k` tend to `+∞` (since `Nf k ≥ (s (idx₀ k)).1 → ∞`).
  have hsize_idx : Tendsto (fun k => (s (idx₀ k)).1) atTop atTop :=
    hsize_atTop.comp hidx₀_mono.tendsto_atTop
  have hN_ge : ∀ k, (s (idx₀ k)).1 ≤ Nf k := fun k => (hplantdata k).size_le
  have hNf_atTop : Tendsto Nf atTop atTop := by
    apply tendsto_atTop_mono hN_ge hsize_idx
  -- A subsequence `idx₁` making `Nf` strictly increasing.
  obtain ⟨idx₁, hidx₁_mono, hidx₁N_mono⟩ := strictMono_subseq_of_tendsto_atTop hNf_atTop
  -- The flag sequence of unlabelled host graphs, with strictly increasing sizes.
  set sH : FlagSeq ∅ₜ := fun k => ⟨Nf (idx₁ k), graphFlag (Hf (idx₁ k))⟩ with hsH
  have hsH_inc : Increases sH := hidx₁N_mono
  -- A convergent subsequence with base limit `φ₀`.
  obtain ⟨a, ϕ, hϕ_mono, hconv_a⟩ :=
    increasing_flagSeq_contain_convergent_subseq sH hsH_inc
  obtain ⟨φ₀, hφ₀⟩ := flagSeq_limit_mem_positiveHom (sH ∘ ϕ) hconv_a
  -- The convergent flag sequence `sHϕ` with limit `φ₀`.
  set sHϕ : FlagSeq ∅ₜ := sH ∘ ϕ with hsHϕ
  have hconv_sHϕ : ConvergesTo sHϕ φ₀.coe := hφ₀ ▸ hconv_a
  -- `n₀ ≤ Nf k` for every `k` (since `n₀ ≤ (s (idx₀ k)).1 ≤ Nf k`).
  have hn₀_le_size : ∀ t, n₀ ≤ (s t).1 := by
    intro t
    have hge := finFlag_size_ge_n₀ (s t)
    exact hge
  have hn₀_Nf : ∀ k, n₀ ≤ Nf k := fun k => le_trans (hn₀_le_size (idx₀ k)) (hN_ge k)
  -- Step 8: `posHomPoint φ₀ ∈ Q₀`.
  have hφ0Q : posHomPoint φ₀ ∈ Qσ (hc.constraintOf σ).forb0 := by
    apply flagSeqLimit_mem_Q0 (hc.constraintOf σ) hconv_sHϕ
    intro k D hD
    -- Each term `(sHϕ k).2 = graphFlag (Hf (idx₁ (ϕ k)))` is in the class, hence forbidden-free.
    show flagDensity₁ D.2 (graphFlag (Hf (idx₁ (ϕ k)))) = 0
    exact hc.forbiddenFree_of_mem (Hf (idx₁ (ϕ k))) (hplantdata (idx₁ (ϕ k))).memH D hD
  -- Step 9: `φ₀ ⟨σ⟩₀ > 0`, via the uniform `δ/3/n₀!` lower bound on the σ-type density.
  set d₀ : ℝ := δ / Nat.factorial n₀ with hd₀
  have hd₀_pos : 0 < d₀ := by rw [hd₀]; positivity
  -- The uniform lower bound on every term of `sHϕ`.
  have htype_lower : ∀ k, d₀ ≤ (flagDensity₁ σ.toEmptyTypeFlag (sHϕ k).2 : ℝ) := by
    intro k
    show d₀ ≤ (flagDensity₁ σ.toEmptyTypeFlag (graphFlag (Hf (idx₁ (ϕ k)))) : ℝ)
    apply flagDensity_type_lower_of_planting (hplantdata (idx₁ (ϕ k))).Θ hδpos.le
    · exact (hplantdata (idx₁ (ϕ k))).card_lb
    · exact hn₀_Nf (idx₁ (ϕ k))
  have hφ0σ : φ₀ ⟨σ⟩₀ > 0 := by
    have hval : φ₀ ⟨σ⟩₀ = φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩ := by
      show φ₀ ⟦basisVector ⟨n₀, σ.toEmptyTypeFlag⟩⟧ = φ₀.coe ⟨n₀, σ.toEmptyTypeFlag⟩
      rw [φ₀.coe_flag]
    rw [hval]
    set F₀ : FinFlag ∅ₜ := ⟨n₀, σ.toEmptyTypeFlag⟩ with hF₀
    have hlim : Tendsto (fun k => flagDensitySeq sHϕ k F₀) atTop (𝓝 (φ₀.coe F₀)) :=
      (flagSeq_convergesTo_iff.mp hconv_sHϕ).2 F₀
    have hge : d₀ ≤ φ₀.coe F₀ := by
      refine ge_of_tendsto' hlim ?_
      intro k
      exact htype_lower k
    linarith
  -- Step 10: rooting measures + weak convergence.
  have hsHϕpos : ∀ k, flagDensity₁ σ.toEmptyTypeFlag (sHϕ k).2 > 0 := by
    intro k
    have := htype_lower k
    have hcast : (0 : ℝ) < (flagDensity₁ σ.toEmptyTypeFlag (sHϕ k).2 : ℝ) := lt_of_lt_of_le hd₀_pos this
    exact_mod_cast hcast
  set P : ℕ → ProbabilityMeasure (FlagDensitySpace σ) := sHϕ.toProbMeasureSeq hsHϕpos with hP
  have hPweak : Tendsto P atTop (𝓝 (rootingMeasureFDS φ₀ hφ0σ)) :=
    tendsto_rootingMeasure_extend hφ0σ sHϕ hsHϕpos hconv_sHϕ
  -- Step 11: cylinder mass.  The closed cylinder centered at `ψ`, radius `2ε/3`.
  set base : FinFlag σ → ℝ := fun Fi => ψ.val Fi with hbase
  set C : Set (FlagDensitySpace σ) := cyl Fs base (2 * ε / 3) with hC
  have hCclosed : IsClosed C := isClosed_cyl Fs base (2 * ε / 3)
  -- For every term, `δ/3/n₀! ≤ (P k)(C).toReal` is too strong; we use `(P k)(C).toReal ≥ d₀`.
  -- The cylinder-mass lower bound: `d₀ ≤ (P k)(C).toReal` for every `k`.
  have hmass : ∀ k, d₀ ≤ ((P k : Measure (FlagDensitySpace σ)) C).toReal := by
    intro k
    -- Abbreviations for the term.
    set j : ℕ := idx₁ (ϕ k) with hj
    set pd := hplantdata j with hpd
    set N := pd.N with hNdef
    set Hgr : SimpleGraph (Fin N) := pd.H with hHgr
    set Θ := pd.Θ with hΘdef
    -- The flag `F = (sHϕ k).2` and its size.
    have hFk2 : (sHϕ k).2 = graphFlag Hgr := rfl
    have hFk1 : (sHϕ k).1 = N := rfl
    -- The σ-density positivity hypothesis for this term.
    have hpos : flagDensity₁ σ.toEmptyTypeFlag (sHϕ k).2 > 0 := hsHϕpos k
    -- The labelling-count form of the measure.
    set Fk : FinFlag ∅ₜ := (sHϕ k) with hFk
    have hFk_eq : Fk = ⟨N, graphFlag Hgr⟩ := rfl
    -- `P k = Fk.toProbMeasure hpos`.
    have hPk : (P k : Measure (FlagDensitySpace σ)) = (Fk.toProbMeasure hpos : Measure (FlagDensitySpace σ)) := rfl
    rw [hPk, toProbMeasure_apply_eq_labeling_ratio Fk hpos C]
    -- The host graph of the labelling count.
    set host' : SimpleGraph (Fin Fk.1) := (Quotient.out Fk.2).graph with hhost'
    -- `graphFlag Hgr = ⟦Hrep⟧`, and `out Fk.2 ≈ Hrep`, giving `host' ≃g Hgr`.
    set Hrep : LabeledGraph ∅ₜ (Fin N) :=
      {graph := Hgr, type_embed := RelEmbedding.ofIsEmpty (∅ₜ).Adj Hgr.Adj} with hHrep
    have hFk2' : Fk.2 = graphFlag Hgr := rfl
    have hgraphFlag : graphFlag Hgr = (⟦Hrep⟧ : Flag ∅ₜ (Fin N)) := rfl
    have hout_eq : (⟦Quotient.out Fk.2⟧ : Flag ∅ₜ (Fin Fk.1)) = (⟦Hrep⟧ : Flag ∅ₜ (Fin N)) := by
      rw [Quotient.out_eq]; rw [hFk2', hgraphFlag]
    have hout_iso : (Quotient.out Fk.2) ≈ Hrep := Quotient.exact hout_eq
    obtain ⟨ψhost⟩ := hout_iso
    -- The host iso `host' ≃g Hgr`.
    have eHostH : host' ≃g Hgr := ψhost.graph_iso
    -- Numerator / denominator labelling sets.
    set numSet := Finset.univ.filter (fun H : LabeledGraph σ (Fin Fk.1) =>
        H.graph = host' ∧ funFromFlagWithSizeToFlagDensitySpace σ Fk.1 (⟦H⟧ : FlagWithSize σ Fk.1) ∈ C)
      with hnumSet
    set denSet := Finset.univ.filter (fun H : LabeledGraph σ (Fin Fk.1) => H.graph = host')
      with hdenSet
    -- Profile membership in `C` unfolds to the cylinder condition.
    have hprofile : ∀ H : LabeledGraph σ (Fin Fk.1),
        (funFromFlagWithSizeToFlagDensitySpace σ Fk.1 (⟦H⟧ : FlagWithSize σ Fk.1) ∈ C)
          ↔ ∀ Fi ∈ Fs, |(flagDensity₁ Fi.2 (⟦H⟧ : Flag σ (Fin Fk.1)) : ℝ) - base Fi| ≤ 2 * ε / 3 := by
      intro H
      rw [hC, cyl, Set.mem_setOf_eq]
      rfl
    -- (1) The denominator is the number of σ-embeddings into `host'`, equal to that into `Hgr`.
    have hden_eq : denSet.card = Fintype.card (σ ↪g Hgr) := by
      rw [hdenSet, card_labelings_eq_card_embeddings host']
      exact Fintype.card_congr (embeddingIsoCongr eHostH)
    -- The denominator is at most `N^{n₀}`.
    have hden_le : (denSet.card : ℝ) ≤ (N : ℝ) ^ n₀ := by
      rw [hden_eq]
      have hle : Fintype.card (σ ↪g Hgr) ≤ N ^ n₀ := by
        calc Fintype.card (σ ↪g Hgr) ≤ Fintype.card (Fin n₀ ↪ Fin N) :=
              Fintype.card_le_of_injective (fun e => e.toEmbedding)
                (fun a b h => RelEmbedding.toEmbedding_inj.mp h)
          _ ≤ Fintype.card (Fin n₀ → Fin N) :=
              Fintype.card_le_of_injective _ Function.Embedding.coe_injective
          _ = N ^ n₀ := by simp
      exact_mod_cast hle
    -- The denominator is positive.
    have hden_pos : (0 : ℝ) < (denSet.card : ℝ) := by
      have h0 : 0 < denSet.card := by
        rw [hden_eq]
        -- An embedding exists since the σ-type density is positive (Θ is nonempty).
        have hΘpos : 0 < Θ.card := by
          have hcl := pd.card_lb
          by_contra hcon
          push_neg at hcon
          have : Θ.card = 0 := Nat.le_zero.mp hcon
          rw [this] at hcl
          simp only [Nat.cast_zero] at hcl
          have hNpow : (0 : ℝ) < (N : ℝ) ^ n₀ := by
            have hNpos : 0 < N := lt_of_lt_of_le hn₀ (hn₀_Nf j)
            positivity
          nlinarith [mul_pos hδpos hNpow]
        obtain ⟨θ', _⟩ := Finset.card_pos.mp hΘpos
        exact Fintype.card_pos_iff.mpr ⟨θ'⟩
      exact_mod_cast h0
    -- (2) Planted embeddings inject into the numerator labellings.
    have hnum_lb : (Θ.card : ℝ) ≤ (numSet.card : ℝ) := by
      have hcard_le : Θ.card ≤ numSet.card := by
        -- The map `θ' ↦ transportLabeled (⟨Hgr, θ'⟩) eHostH.symm`.
        rw [← Fintype.card_coe numSet]
        rw [← Fintype.card_coe Θ]
        apply Fintype.card_le_of_injective
          (fun θ' => ⟨transportLabeled (G := (⟨Hgr, θ'.1⟩ : LabeledGraph σ (Fin N))) eHostH.symm, by
            rw [hnumSet, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, rfl, ?_⟩
            rw [hprofile]
            intro Fi hFi
            -- The transported labelling is `≃f` the labelling `⟨Hgr, θ'⟩`.
            have hiso : (transportLabeled (G := (⟨Hgr, θ'.1⟩ : LabeledGraph σ (Fin N))) eHostH.symm)
                ≃f (⟨Hgr, θ'.1⟩ : LabeledGraph σ (Fin N)) :=
              (transportLabeled_iso (G := (⟨Hgr, θ'.1⟩ : LabeledGraph σ (Fin N))) eHostH.symm).symm
            have hdens : (flagDensity₁ Fi.2
                  (⟦transportLabeled (G := (⟨Hgr, θ'.1⟩ : LabeledGraph σ (Fin N))) eHostH.symm⟧
                    : Flag σ (Fin Fk.1)) : ℝ)
                = (flagDensity₁ Fi.2 (⟦(⟨Hgr, θ'.1⟩ : LabeledGraph σ (Fin N))⟧ : Flag σ (Fin N)) : ℝ) := by
              have h := flagDensity₁_respect_eqv Fi hiso
              exact_mod_cast h
            rw [hdens]
            -- planting clause (iii) + density-closeness give `≤ 2ε/3`.
            have hKi := hK (idx₀ j) (hidx₀_ge j)
            have hclose := pd.close θ'.1 θ'.2 Fi (hmFs Fi hFi)
            -- `pd` is built from `(s (idx₀ j)).2.out`; rewrite `⟦out⟧` to `(s ·).2`.
            have hbaseflag : (⟦(s (idx₀ j)).2.out⟧ : Flag σ (Fin (s (idx₀ j)).1)) = (s (idx₀ j)).2 :=
              Quotient.out_eq _
            rw [hbaseflag] at hclose
            -- planting clause: within `ε/3` of the `idx₀ j`-th flag densities.
            have hclose' : |(flagDensity₁ Fi.2
                  (⟦(⟨Hgr, θ'.1⟩ : LabeledGraph σ (Fin N))⟧ : Flag σ (Fin N)) : ℝ)
                - (flagDensity₁ Fi.2 (s (idx₀ j)).2 : ℝ)| < ε / 3 := hclose
            -- density-closeness of the `idx₀ j`-th flag to `ψ`.
            have hKi2 := hKi.2 Fi hFi
            calc |(flagDensity₁ Fi.2 (⟦(⟨Hgr, θ'.1⟩ : LabeledGraph σ (Fin N))⟧ : Flag σ (Fin N)) : ℝ)
                  - base Fi|
                ≤ |(flagDensity₁ Fi.2 (⟦(⟨Hgr, θ'.1⟩ : LabeledGraph σ (Fin N))⟧ : Flag σ (Fin N)) : ℝ)
                    - (flagDensity₁ Fi.2 (s (idx₀ j)).2 : ℝ)|
                  + |(flagDensity₁ Fi.2 (s (idx₀ j)).2 : ℝ) - base Fi| := abs_sub_le _ _ _
              _ ≤ ε / 3 + ε / 3 := by
                  rw [hbase]
                  exact add_le_add hclose'.le hKi2.le
              _ = 2 * ε / 3 := by ring⟩)
          ?_
        -- injectivity of `θ' ↦ transported labelling`
        intro θ'₁ θ'₂ heq
        have heq' : transportLabeled (G := (⟨Hgr, θ'₁.1⟩ : LabeledGraph σ (Fin N))) eHostH.symm
            = transportLabeled (G := (⟨Hgr, θ'₂.1⟩ : LabeledGraph σ (Fin N))) eHostH.symm :=
          Subtype.ext_iff.mp heq
        -- Their type-embedding functions (as plain functions) agree.
        have hte : ∀ i : Fin n₀,
            (eHostH.symm.toEmbedding.comp θ'₁.1) i = (eHostH.symm.toEmbedding.comp θ'₂.1) i := by
          have := congrArg (fun H : LabeledGraph σ (Fin Fk.1) =>
            (H.type_embed : Fin n₀ → Fin Fk.1)) heq'
          intro i
          exact congrFun this i
        -- Cancel the injective `eHostH.symm` to get `θ'₁ = θ'₂`.
        apply Subtype.ext
        apply RelEmbedding.toEmbedding_inj.mp
        apply Function.Embedding.ext
        intro i
        have h2 := hte i
        simp only [SimpleGraph.Embedding.coe_comp, Function.comp_apply, SimpleGraph.Iso.toEmbedding,
          RelIso.coe_toRelEmbedding] at h2
        exact eHostH.symm.injective h2
      exact_mod_cast hcard_le
    -- Conclude: ratio `≥ Θ.card / N^{n₀} ≥ δ ≥ d₀ = δ/n₀!`.
    have hratio_lb : δ ≤ (numSet.card : ℝ) / (denSet.card : ℝ) := by
      have hcard_lb := pd.card_lb
      -- `δ · N^{n₀} ≤ Θ.card ≤ numSet.card`, and `denSet.card ≤ N^{n₀}`.
      rw [le_div_iff₀ hden_pos]
      calc δ * (denSet.card : ℝ)
          ≤ δ * (N : ℝ) ^ n₀ := by
            apply mul_le_mul_of_nonneg_left hden_le hδpos.le
        _ ≤ (Θ.card : ℝ) := hcard_lb
        _ ≤ (numSet.card : ℝ) := hnum_lb
    have hd₀_le : d₀ ≤ δ := by
      rw [hd₀]
      have hfact1 : (1 : ℝ) ≤ (Nat.factorial n₀ : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n₀)
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hδpos.le]
    exact le_trans hd₀_le hratio_lb
  -- Step 12: portmanteau + support tail.
  have hlimsup : (atTop.limsup fun k => (P k : Measure (FlagDensitySpace σ)) C)
      ≤ (rootingMeasureFDS φ₀ hφ0σ : Measure (FlagDensitySpace σ)) C :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hPweak hCclosed
  have hc_event' : ∀ᶠ k in atTop, ENNReal.ofReal d₀ ≤ (P k : Measure (FlagDensitySpace σ)) C := by
    filter_upwards with k
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hmass k)
  have hge : ENNReal.ofReal d₀ ≤ atTop.limsup fun k => (P k : Measure (FlagDensitySpace σ)) C :=
    le_limsup_of_frequently_le (hc_event'.frequently) (by isBoundedDefault)
  have hroot_ge : ENNReal.ofReal d₀
      ≤ (rootingMeasureFDS φ₀ hφ0σ : Measure (FlagDensitySpace σ)) C :=
    le_trans hge hlimsup
  have hmap : (rootingMeasureFDS φ₀ hφ0σ : Measure (FlagDensitySpace σ)) C
      = (ℙ[φ₀] : Measure (PositiveHomSpace σ)) (Subtype.val ⁻¹' C) := by
    rw [rootingMeasureFDS, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (measurable_subtype_coe) hCclosed.measurableSet]
  set CP : Set (PositiveHomSpace σ) := Subtype.val ⁻¹' C with hCP
  have hCP_pos : (0 : ENNReal) < (ℙ[φ₀] : Measure (PositiveHomSpace σ)) CP := by
    rw [hmap] at hroot_ge
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hd₀_pos) hroot_ge
  obtain ⟨χ, hχsupp, hχCP⟩ :
      ∃ χ, χ ∈ (ℙ[φ₀] : Measure (PositiveHomSpace σ)).support ∧ χ ∈ CP := by
    by_contra hcon
    push_neg at hcon
    have hsub : CP ⊆ (ℙ[φ₀] : Measure (PositiveHomSpace σ)).supportᶜ := by
      intro χ hχ
      exact fun hχs => hcon χ hχs hχ
    have hzero : (ℙ[φ₀] : Measure (PositiveHomSpace σ)) CP = 0 :=
      measure_mono_null hsub (Measure.measure_compl_support)
    rw [hzero] at hCP_pos
    exact lt_irrefl 0 hCP_pos
  refine ⟨χ, ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨φ₀, Set.mem_iUnion.mpr ⟨hφ0Q,
      Set.mem_iUnion.mpr ⟨hφ0σ, hχsupp⟩⟩⟩
  · intro Fi hFi
    have hχbase : |χ.val Fi - base Fi| ≤ 2 * ε / 3 := hχCP Fi hFi
    rw [hbase] at hχbase
    calc |χ.val Fi - ψ.val Fi| ≤ 2 * ε / 3 := hχbase
      _ < ε := by linarith

end FlagAlgebras.MetaTheory
