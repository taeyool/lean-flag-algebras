import LeanFlagAlgebras.MetaTheory.CertificateSliceVanishing
import LeanFlagAlgebras.MetaTheory.GraphClassConstraint
import LeanFlagAlgebras.MetaTheory.EdgeObstruction
import LeanFlagAlgebras.MetaTheory.C4Free
import LeanFlagAlgebras.MetaTheory.DenseObstruction
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-! # The balanced complete multipartite limit and the Turán slices (paper §11.5,
the existence half of `thm:turan-slice` / `thm:relative-mantel`)

The Turán graphs `turanGraph (r·n) r` (Mathlib: `Adj v w ↔ v % r ≠ w % r`) form a
`K_{r+1}`-free flag sequence of increasing sizes whose edge density tends to `(r-1)/r`.  A
convergent subsequence produces a constrained unlabelled limit — the balanced complete
`r`-partite limit — witnessing that the **Turán slice**

  `Y_Tur^{(r)} = {φ₀ ∈ Q₀^{(r)} : φ₀(ρ) = (r-1)/r}`

is nonempty (`turanSlice_nonempty`); at `r = 2` this is the **Mantel slice** of
`thm:relative-mantel` (`mantelSlice_nonempty`).  Here `ρ` is the §9 unlabelled edge-density
element (`EdgeObstruction`), whose evaluation at a graph flag is the graph's edge density
(`flagDensity_unlabelledEdge_eq` + `downwardNormalizingFactor_edge_eq_one`, §9.1–§9.2).

The uniqueness half of `thm:turan-slice` (`Y_Tur^{(r)}` is a SINGLE point) is the
Erdős–Simonovits stability theorem — classical input outside this development (and outside
Mathlib); the support identities it powers are future work (README deviation).
-/

open MeasureTheory Filter SimpleGraph
open scoped Topology

namespace FlagAlgebras.MetaTheory

/-! ## The Turán flag sequence -/

/-- The Turán flag sequence: the flag of `turanGraph (r·(n+1)) r` (nonempty sizes). -/
noncomputable def turanFlagSeq (r : ℕ) : FlagSeq ∅ₜ :=
  fun n => ⟨r * (n + 1), graphFlag (turanGraph (r * (n + 1)) r)⟩

/-- The Turán graphs are `K_{r+1}`-free (Mathlib), so the sequence is in-class. -/
lemma turanFlagSeq_cliqueFree (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    (turanGraph (r * (n + 1)) r).CliqueFree (r + 1) :=
  turanGraph_cliqueFree (by omega)

/-! ### Counting the edges of `turanGraph (r·m) r` -/

/-- Twice `C(m,2)` is `m·(m-1)` (the `Nat`-subtraction-friendly form of `choose_two_right`). -/
private lemma two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  rw [Nat.choose_two_right]
  apply Nat.mul_div_cancel'
  rcases m with _ | k
  · simp
  · rw [Nat.add_sub_cancel, Nat.mul_comm]
    exact (Nat.even_mul_succ_self k).two_dvd

/-- Each residue class `{v : Fin (r·m) | v % r = i}` (with `i < r`) has exactly `m`
elements, via the explicit bijection `j ↦ i + r·j` from `Fin m`. -/
private lemma card_residue_class (r m i : ℕ) (hi : i < r) :
    (Finset.univ.filter (fun v : Fin (r * m) => v.val % r = i)).card = m := by
  have hr : 0 < r := by omega
  have hb : ∀ j : Fin m, i + r * j.val < r * m := by
    intro j
    have hj := j.isLt
    have h1 : r * (j.val + 1) ≤ r * m := Nat.mul_le_mul (Nat.le_refl r) (by omega)
    rw [Nat.mul_succ] at h1
    omega
  have himg : Finset.univ.filter (fun v : Fin (r * m) => v.val % r = i)
      = Finset.univ.image (fun j : Fin m => (⟨i + r * j.val, hb j⟩ : Fin (r * m))) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hv
      have hdiv : v.val / r < m := by
        rw [Nat.div_lt_iff_lt_mul hr]
        calc v.val < r * m := v.isLt
          _ = m * r := Nat.mul_comm r m
      refine ⟨⟨v.val / r, hdiv⟩, ?_⟩
      apply Fin.ext
      show i + r * (v.val / r) = v.val
      rw [← hv]
      exact Nat.mod_add_div v.val r
    · rintro ⟨j, rfl⟩
      show (i + r * j.val) % r = i
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hi
  have hinj : Function.Injective (fun j : Fin m => (⟨i + r * j.val, hb j⟩ : Fin (r * m))) := by
    intro j1 j2 hj
    have h1 : i + r * j1.val = i + r * j2.val := congrArg Fin.val hj
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hr (show r * j1.val = r * j2.val by omega))
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- In the complement of the Turán graph (the disjoint union of `r` residue-class cliques),
every vertex has degree `m - 1`: its neighbours are the other members of its residue class. -/
private lemma turanGraph_compl_degree (r m : ℕ) (hr : 1 ≤ r) (v : Fin (r * m)) :
    (turanGraph (r * m) r)ᶜ.degree v = m - 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hnb : (turanGraph (r * m) r)ᶜ.neighborFinset v
      = (Finset.univ.filter (fun w : Fin (r * m) => w.val % r = v.val % r)).erase v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj, turanGraph_adj, not_not,
      Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, heq⟩
      exact ⟨fun h => hne h.symm, heq.symm⟩
    · rintro ⟨hne, heq⟩
      exact ⟨fun h => hne h.symm, heq.symm⟩
  have hvmem : v ∈ Finset.univ.filter (fun w : Fin (r * m) => w.val % r = v.val % r) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, rfl⟩
  rw [hnb, Finset.card_erase_of_mem hvmem,
    card_residue_class r m (v.val % r) (Nat.mod_lt _ (by omega))]

/-- `Finset.card` of the edge finset does not depend on the `Fintype` instance carried by
the edge set (`Fintype` is a subsingleton). -/
private lemma edgeFinset_card_congr {V : Type} (G : SimpleGraph V)
    (i j : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset _ G i).card = (@SimpleGraph.edgeFinset _ G j).card := by
  rw [Subsingleton.elim i j]

/-- The complement of `turanGraph (r·m) r` has exactly `r·C(m,2)` edges, by the degree-sum
formula: all `r·m` vertices have complement-degree `m - 1`. -/
private lemma turanGraph_compl_edge_count_aux (r m : ℕ) (hr : 1 ≤ r) :
    ((turanGraph (r * m) r)ᶜ.edgeFinset).card = r * m.choose 2 := by
  have hsum : ∑ v : Fin (r * m), (turanGraph (r * m) r)ᶜ.degree v = r * m * (m - 1) := by
    rw [Finset.sum_congr rfl (fun v _ => turanGraph_compl_degree r m hr v), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h2e : 2 * ((turanGraph (r * m) r)ᶜ.edgeFinset).card = r * m * (m - 1) := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
    exact hsum
  have h2c : 2 * (r * m.choose 2) = r * m * (m - 1) := by
    calc 2 * (r * m.choose 2) = r * (2 * m.choose 2) := by ring
      _ = r * (m * (m - 1)) := by rw [two_mul_choose_two]
      _ = r * m * (m - 1) := by rw [Nat.mul_assoc]
  omega

/-- Instance-generalized form of `turanGraph_compl_edge_count_aux`. -/
private lemma turanGraph_compl_edge_count (r m : ℕ) (hr : 1 ≤ r)
    {j : Fintype ((turanGraph (r * m) r)ᶜ.edgeSet)} :
    (@SimpleGraph.edgeFinset _ (turanGraph (r * m) r)ᶜ j).card = r * m.choose 2 := by
  have h := turanGraph_compl_edge_count_aux r m hr
  rw [edgeFinset_card_congr _ _ j] at h
  exact h

/-- A graph and its complement partition the edges of `⊤`: `e(G) + e(Gᶜ) = C(N,2)`
(private copy of the corresponding counting step in `DenseObstruction`). -/
private lemma card_edgeFinset_add_compl_aux {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = N.choose 2 := by
  have htop : (⊤ : SimpleGraph (Fin N)).edgeFinset.card = N.choose 2 := by
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  rw [← Finset.card_union_of_disjoint (disjoint_edgeFinset.mpr disjoint_compl_right), ← htop]
  congr 1
  ext e
  induction e with
  | _ a b =>
    simp only [Finset.mem_union, mem_edgeFinset, mem_edgeSet, top_adj, compl_adj]
    constructor
    · rintro (h | ⟨hne, _⟩)
      · exact G.ne_of_adj h
      · exact hne
    · intro hne
      by_cases hab : G.Adj a b
      · exact Or.inl hab
      · exact Or.inr ⟨hne, hab⟩

/-- Instance-generalized form of `card_edgeFinset_add_compl_aux`. -/
private lemma card_edgeFinset_add_compl {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj]
    {i : Fintype G.edgeSet} {j : Fintype Gᶜ.edgeSet} :
    (@SimpleGraph.edgeFinset _ G i).card + (@SimpleGraph.edgeFinset _ Gᶜ j).card
      = N.choose 2 := by
  have h := card_edgeFinset_add_compl_aux G
  rw [edgeFinset_card_congr _ _ i, edgeFinset_card_congr _ _ j] at h
  exact h

/-- The Turán edge count, stated for an arbitrary `Fintype` instance on the edge set so it
can rewrite the (differently-elaborated) count inside `flagDensity_unlabelledEdge_eq`. -/
private lemma turanGraph_edge_count_aux (r m : ℕ) (hr : 1 ≤ r)
    {i : Fintype ((turanGraph (r * m) r).edgeSet)} :
    (@SimpleGraph.edgeFinset _ (turanGraph (r * m) r) i).card
      = (r * m).choose 2 - r * m.choose 2 := by
  have hpart := card_edgeFinset_add_compl (turanGraph (r * m) r)
    (i := i) (j := inferInstance)
  have hcompl := turanGraph_compl_edge_count r m hr (j := inferInstance)
  rw [← hcompl]
  omega

/-- The edge count of `turanGraph (r·m) r`: all pairs minus the `r` residue classes'
internal pairs, `C(rm, 2) - r·C(m, 2)`. -/
lemma turanGraph_edge_count (r m : ℕ) (hr : 1 ≤ r) :
    (turanGraph (r * m) r).edgeFinset.card
      = (r * m).choose 2 - r * m.choose 2 :=
  -- Count the complement: non-adjacent pairs are pairs with equal residue mod `r`; the
  -- residue classes of `Fin (r·m)` each have `m` elements (`card_residue_class`), so the
  -- complement is a union of `r` cliques of size `m` with `r·C(m,2)` edges
  -- (`turanGraph_compl_edge_count`), and `card_edgeFinset_add_compl` converts.
  turanGraph_edge_count_aux r m hr

/-- The edge density of the Turán flags tends to `(r-1)/r`: the evaluation of the
`ρ`-density at the `n`-th flag is `e(G)/C(N,2)` (§9.1's `flagDensity_unlabelledEdge_eq`),
and the ratio `(C(rm,2) - r·C(m,2))/C(rm,2) → 1 - 1/r`. -/
lemma turanFlagSeq_edge_density_tendsto (r : ℕ) (hr : 2 ≤ r) :
    Tendsto
      (fun n => (flagDensity₁ unlabelledEdgeFlag (turanFlagSeq r n).2 : ℝ))
      atTop (𝓝 (((r : ℝ) - 1) / r)) := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  -- Closed form of each term: `1 - n / (r·(n+1) - 1)`.
  have key : ∀ n : ℕ, (flagDensity₁ unlabelledEdgeFlag (turanFlagSeq r n).2 : ℝ)
      = 1 - (n : ℝ) / ((r : ℝ) * ((n : ℝ) + 1) - 1) := by
    intro n
    have hr1 : 1 ≤ r := by omega
    have h2rm : 2 ≤ r * (n + 1) := by
      have h1 : 2 * 1 ≤ r * (n + 1) := Nat.mul_le_mul hr (by omega)
      omega
    have hapos : 0 < (r * (n + 1)).choose 2 := Nat.choose_pos h2rm
    have hpart := card_edgeFinset_add_compl (turanGraph (r * (n + 1)) r)
      (i := inferInstance) (j := inferInstance)
    have hcompl := turanGraph_compl_edge_count r (n + 1) hr1 (j := inferInstance)
    have hle : r * (n + 1).choose 2 ≤ (r * (n + 1)).choose 2 := by
      rw [← hcompl]
      omega
    -- The `ρ`-density of the `n`-th flag, with the edge count substituted.
    have hd : flagDensity₁ unlabelledEdgeFlag (turanFlagSeq r n).2
        = (((r * (n + 1)).choose 2 - r * (n + 1).choose 2 : ℕ) : ℚ)
          / (((r * (n + 1)).choose 2 : ℕ) : ℚ) := by
      have h := flagDensity_unlabelledEdge_eq (turanGraph (r * (n + 1)) r)
      rw [turanGraph_edge_count_aux r (n + 1) hr1] at h
      exact h
    rw [hd, Nat.cast_sub hle]
    push_cast
    rw [Nat.cast_choose_two ℝ (r * (n + 1)), Nat.cast_choose_two ℝ (n + 1)]
    push_cast
    have h2rmR : (2 : ℝ) ≤ (r : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast h2rm
    have hne1 : (r : ℝ) * ((n : ℝ) + 1) - 1 ≠ 0 :=
      ne_of_gt (by linarith : (0 : ℝ) < (r : ℝ) * ((n : ℝ) + 1) - 1)
    have hne0 : (r : ℝ) * ((n : ℝ) + 1) ≠ 0 :=
      ne_of_gt (by linarith : (0 : ℝ) < (r : ℝ) * ((n : ℝ) + 1))
    field_simp
    ring
  -- The rational-function limit `1 - n / (r·(n+1) - 1) → 1 - 1/r`.
  have hdiv : Tendsto (fun n : ℕ => ((r : ℝ) - 1) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat ((r : ℝ) - 1)
  have hden : Tendsto (fun n : ℕ => (r : ℝ) + ((r : ℝ) - 1) / n) atTop (𝓝 ((r : ℝ) + 0)) :=
    tendsto_const_nhds.add hdiv
  rw [add_zero] at hden
  have hfrac0 : Tendsto (fun n : ℕ => 1 / ((r : ℝ) + ((r : ℝ) - 1) / n)) atTop
      (𝓝 (1 / (r : ℝ))) :=
    tendsto_const_nhds.div hden (by linarith : (r : ℝ) ≠ 0)
  have hfrac : Tendsto (fun n : ℕ => (n : ℝ) / ((r : ℝ) * ((n : ℝ) + 1) - 1)) atTop
      (𝓝 (1 / (r : ℝ))) := by
    refine hfrac0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnne : (n : ℝ) ≠ 0 := by linarith
    have hden2 : (r : ℝ) + ((r : ℝ) - 1) / n = ((r : ℝ) * ((n : ℝ) + 1) - 1) / n := by
      rw [eq_div_iff hnne, add_mul, div_mul_cancel₀ _ hnne]
      ring
    rw [hden2, one_div_div]
  have hlim : Tendsto (fun n : ℕ => 1 - (n : ℝ) / ((r : ℝ) * ((n : ℝ) + 1) - 1)) atTop
      (𝓝 (1 - 1 / (r : ℝ))) := tendsto_const_nhds.sub hfrac
  have hr0 : (r : ℝ) ≠ 0 := by linarith
  have hval : (1 : ℝ) - 1 / (r : ℝ) = ((r : ℝ) - 1) / r := by
    rw [sub_div, div_self hr0]
  rw [← hval]
  exact hlim.congr (fun n => (key n).symm)

/-! ## The balanced multipartite limit and slice nonemptiness -/

/-- **The balanced complete `r`-partite limit exists**: a constrained unlabelled limit of
the `K_{r+1}`-free class with edge density `φ(ρ) = (r-1)/r`. -/
theorem exists_turan_limit (r : ℕ) (hr : 2 ≤ r) :
    ∃ φ : PositiveHom ∅ₜ,
      posHomPoint φ ∈ Qσ (constraintOf (cliqueFreeClass (r + 1)) ∅ₜ).forb0
        ∧ φ ρ = ((r : ℝ) - 1) / r := by
  -- The sequence has strictly increasing sizes; extract a convergent subsequence and its
  -- limit homomorphism.
  have hinc : Increases (turanFlagSeq r) := by
    apply increases_of_consecutive_lt
    intro n
    show r * (n + 1) < r * (n + 2)
    have h0 : 0 < r := by omega
    calc r * (n + 1) < r * (n + 1) + r := by omega
      _ = r * (n + 2) := by ring
  obtain ⟨a, ϕ, hmono, hconv⟩ :=
    increasing_flagSeq_contain_convergent_subseq (turanFlagSeq r) hinc
  obtain ⟨φ, hφ⟩ := flagSeq_limit_mem_positiveHom (turanFlagSeq r ∘ ϕ) hconv
  obtain ⟨-, hpt⟩ := flagSeq_convergesTo_iff.mp hconv
  refine ⟨φ, ?_, ?_⟩
  · -- Constrainedness: each flag's graph is `CliqueFree (r+1)`, so every forbidden flag has
    -- density `0` along the sequence, hence value `0` in the limit.
    rw [mem_Qσ_iff]
    intro D hD
    rw [posHomPoint_val_apply, ← PositiveHom.coe_flag, hφ]
    have hzero : ∀ k, flagDensitySeq (turanFlagSeq r ∘ ϕ) k D = 0 := by
      intro k
      show (flagDensity₁ D.2 (turanFlagSeq r (ϕ k)).2 : ℝ) = 0
      exact_mod_cast
        (cliqueFreeClass (r + 1)).toHeredClass.forbiddenFree_of_mem (σ := ∅ₜ)
          (turanGraph (r * (ϕ k + 1)) r)
          (turanFlagSeq_cliqueFree r (by omega) (ϕ k)) D hD
    have hlim : Tendsto (fun k => flagDensitySeq (turanFlagSeq r ∘ ϕ) k D) atTop
        (𝓝 (a D)) := hpt D
    rw [tendsto_congr hzero, tendsto_const_nhds_iff] at hlim
    exact hlim.symm
  · -- The `ρ`-value: `φ ρ` is the unlabelled-edge density coefficient of the limit
    -- (the normaliser is `1` by §9.2), which is the limit of the Turán edge densities.
    have hedgeunlabel : (⟨edgeFF.1, unlabel edgeFF.2⟩ : FinFlag ∅ₜ) = ⟨2, unlabelledEdgeFlag⟩ :=
      rfl
    have hρval : φ ρ
        = (downwardNormalizingFactor edgeFF.2 : ℝ) * φ.coe ⟨2, unlabelledEdgeFlag⟩ := by
      show φ (downward e) = _
      rw [e, downward_basisVector, PositiveHom.map_smul, hedgeunlabel, ← PositiveHom.coe_flag]
    rw [downwardNormalizingFactor_edge_eq_one] at hρval
    have hcoe : φ.coe ⟨2, unlabelledEdgeFlag⟩ = a ⟨2, unlabelledEdgeFlag⟩ := by rw [hφ]
    have h1 : Tendsto (fun k => flagDensitySeq (turanFlagSeq r ∘ ϕ) k ⟨2, unlabelledEdgeFlag⟩)
        atTop (𝓝 (a ⟨2, unlabelledEdgeFlag⟩)) := hpt _
    have h2 : Tendsto (fun k => flagDensitySeq (turanFlagSeq r ∘ ϕ) k ⟨2, unlabelledEdgeFlag⟩)
        atTop (𝓝 (((r : ℝ) - 1) / r)) :=
      (turanFlagSeq_edge_density_tendsto r hr).comp hmono.tendsto_atTop
    have huniq : a ⟨2, unlabelledEdgeFlag⟩ = ((r : ℝ) - 1) / r := tendsto_nhds_unique h1 h2
    rw [hρval, hcoe, huniq]
    norm_num

/-- The Turán slice `Y_Tur^{(r)}` (the equality slice of `ρ` at `(r-1)/r`). -/
noncomputable def turanSlice (r : ℕ) : Set (PositiveHomSpace ∅ₜ) :=
  eqSlice (constraintOf (cliqueFreeClass (r + 1)) ∅ₜ).forb0 ρ (((r : ℝ) - 1) / r)

/-- **The Turán slice is nonempty** (the existence half of `thm:turan-slice`). -/
theorem turanSlice_nonempty (r : ℕ) (hr : 2 ≤ r) : (turanSlice r).Nonempty := by
  obtain ⟨φ, hQ, hρ⟩ := exists_turan_limit r hr
  exact ⟨posHomPoint φ, posHomPoint_mem_eqSlice.mpr ⟨hQ, hρ⟩⟩

/-- The Mantel slice (`thm:relative-mantel`): the `r = 2` Turán slice — triangle-free
limits of edge density `1/2`. -/
noncomputable def mantelSlice : Set (PositiveHomSpace ∅ₜ) := turanSlice 2

/-- **The Mantel slice is nonempty** (the existence half of `thm:relative-mantel`). -/
theorem mantelSlice_nonempty : mantelSlice.Nonempty :=
  turanSlice_nonempty 2 (by norm_num)

end FlagAlgebras.MetaTheory
