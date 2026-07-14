import LeanFlagAlgebras.MetaTheory.RelativePlanted
import LeanFlagAlgebras.MetaTheory.TuranLimit
import LeanFlagAlgebras.MetaTheory.DenseObstruction

/-! # Slices break root-plantability: the Mantel slice (paper §11.4,
`prop:mantel-not-plantable`)

The relative avatar of the pinning phenomenon.  Root the one-vertex type at an **isolated
vertex added to `K_{n+1,n+1}`**: the underlying graphs are triangle-free with edge density
`→ 1/2`, so they converge into the Mantel slice, and the rooted views converge to a
`Y_Mantel`-planted view `χ` with rooted edge density `χ(e) = 0`.  But every point of the
relative *support* pins `e` to `1/2` (`thm:relative-mantel` (i)), so
`S_vtype(Y_Mantel) ⊊ Q_vtype(Y_Mantel)` — although the triangle-free class itself is
root-plantable at every type (`cor:clique-free`).

The pinning input `hpin` is `thm:relative-mantel` (i); its proof (the Erdős–Simonovits
uniqueness of the extremal Mantel limit plus the Dirac extension computation for the
balanced bipartite graphon) is classical input not formalised in this development, so it
enters as an explicit hypothesis (README deviation, standing practice for classical
inputs).  Everything else — the planted witness and the strict inclusion — is proved.

The host graph `knnPlusW n` is bipartite-by-parity on the first `2(n+1)` of `2(n+1)+1`
vertices, with the last vertex isolated (the root).
-/

open MeasureTheory Filter SimpleGraph
open scoped Topology

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-! ## The host graph `K_{n+1,n+1} + w` -/

/-- `K_{n+1,n+1}` (bipartition by parity on the first `2(n+1)` vertices) together with one
additional isolated vertex (the last one). -/
def knnPlusW (n : ℕ) : SimpleGraph (Fin (2 * (n + 1) + 1)) where
  Adj i j := i.val % 2 ≠ j.val % 2 ∧ i.val < 2 * (n + 1) ∧ j.val < 2 * (n + 1)
  symm := by
    intro i j ⟨hp, hi, hj⟩
    exact ⟨fun h => hp h.symm, hj, hi⟩
  loopless := by
    intro i ⟨hp, _, _⟩
    exact hp rfl

/-- `K_{n+1,n+1} + w` is triangle-free: a triangle needs three pairwise distinct parities,
and there are only two. -/
lemma knnPlusW_cliqueFree (n : ℕ) : (knnPlusW n).CliqueFree 3 := by
  -- Take a 3-clique `t`; among its three vertices two share a parity (`Finset` pigeonhole
  -- on `val % 2 < 2`, or case analysis via `Finset.card_eq_three` obtaining `a b c`), and
  -- those two are adjacent by `IsNClique`, contradicting the first conjunct of `Adj`.
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  have hAB : (knnPlusW n).Adj a b := ht.1 (by simp) (by simp) hab
  have hAC : (knnPlusW n).Adj a c := ht.1 (by simp) (by simp) hac
  have hBC : (knnPlusW n).Adj b c := ht.1 (by simp) (by simp) hbc
  have h1 : a.val % 2 ≠ b.val % 2 := hAB.1
  have h2 : a.val % 2 ≠ c.val % 2 := hAC.1
  have h3 : b.val % 2 ≠ c.val % 2 := hBC.1
  omega

/-- The last vertex (the root-to-be) is isolated. -/
lemma knnPlusW_last_isolated (n : ℕ) (j : Fin (2 * (n + 1) + 1)) :
    ¬ (knnPlusW n).Adj (Fin.last _) j := by
  -- `(Fin.last _).val = 2*(n+1)` fails the `< 2*(n+1)` conjunct.
  rintro ⟨-, hlt, -⟩
  simp [Fin.last] at hlt

/-! ## The rooted flag sequence -/

/-- The one-vertex-rooted labelled graph: `knnPlusW n` rooted at the isolated last vertex.
(`vtype = ⊥` needs no edge condition; mirror the star/co-star constructions of
`StarWitness`.) -/
noncomputable def knnPlusWLabeled (n : ℕ) : LabeledGraph vtype (Fin (2 * (n + 1) + 1)) where
  graph := knnPlusW n
  type_embed :=
    { toFun := fun _ => Fin.last _
      inj' := fun a b _ => Subsingleton.elim a b
      map_rel_iff' := by
        intro a b
        simp only [vtype, bot_adj]
        constructor
        · intro h; exact knnPlusW_last_isolated n _ h
        · intro h; exact h.elim }

/-- The rooted flag sequence `(K_{n+1,n+1} + w, w)`. -/
noncomputable def mantelRootedSeq : FlagSeq vtype :=
  fun n => ⟨2 * (n + 1) + 1, (⟦knnPlusWLabeled n⟧ : Flag vtype (Fin (2 * (n + 1) + 1)))⟩

/-- The rooted edge flag has density `0` in every term: the root is isolated, so no vertex
subset containing it induces the one-root edge flag `edgeFF`.  (Mirror
`coStar_edge_density` in `StarWitness`, which computes exactly this vanishing for a
different isolated-root host.) -/
lemma mantelRootedSeq_edge_density_zero (n : ℕ) :
    flagDensity₁ edgeFF.2 (mantelRootedSeq n).2 = 0 := by
  by_contra hne
  -- A nonzero density yields a vertex subset containing the root and inducing the edge flag.
  have hne' : flagDensity₁ (⟦edgeLabeled⟧ : Flag vtype (Fin 2))
      (⟦knnPlusWLabeled n⟧ : Flag vtype (Fin (2 * (n + 1) + 1))) ≠ 0 := hne
  obtain ⟨S, hroot, ⟨φ⟩⟩ :=
    exists_inducing_subset_of_flagDensity₁_ne_zero edgeLabeled (knnPlusWLabeled n) hne'
  set IG := LabeledSubgraph.inducedLabeledSubgraph (knnPlusWLabeled n)
    (↑S : Set (Fin (2 * (n + 1) + 1))) hroot with hIGdef
  -- The root of the induced flag and the preimage of the non-root edge endpoint.
  set r : IG.subgraph.verts := IG.coe.type_embed 0 with hrdef
  set w : IG.subgraph.verts := φ.graph_iso.symm 1 with hwdef
  -- Their images under the iso are the two (distinct, hence adjacent) edge vertices.
  have himg_r : φ.graph_iso r = 0 := congrFun φ.type_preserve 0
  have himg_w : φ.graph_iso w = 1 := φ.graph_iso.apply_symm_apply 1
  have h01 : edgeLabeled.graph.Adj (0 : Fin 2) 1 := by
    show (⊤ : SimpleGraph (Fin 2)).Adj 0 1
    rw [SimpleGraph.top_adj]
    decide
  have hadj_img : edgeLabeled.graph.Adj (φ.graph_iso r) (φ.graph_iso w) := by
    rw [himg_r, himg_w]; exact h01
  -- Pull the adjacency back to the host graph.
  have hadj : IG.coe.graph.Adj r w := φ.graph_iso.map_rel_iff.mp hadj_img
  have hadjG : (knnPlusW n).Adj (r : Fin (2 * (n + 1) + 1)) w :=
    ((LabeledSubgraph.coe_adj_iff IG r w).mp hadj).2.2
  -- But the root is the isolated last vertex.
  have hrval : (r : Fin (2 * (n + 1) + 1)) = Fin.last (2 * (n + 1)) := IG.embed_eq 0
  rw [hrval] at hadjG
  exact knnPlusW_last_isolated n w hadjG

/-- Every bipartite vertex (value `< 2(n+1)`) of `knnPlusW n` has degree `n+1`: its
neighbours are exactly the `n+1` opposite-parity values among the first `2(n+1)`. -/
private lemma knnPlusW_degree_lt (n : ℕ) (v : Fin (2 * (n + 1) + 1))
    (hv : v.val < 2 * (n + 1)) : (knnPlusW n).degree v = n + 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hnb : (knnPlusW n).neighborFinset v
      = Finset.univ.filter
          (fun j : Fin (2 * (n + 1) + 1) => j.val % 2 ≠ v.val % 2 ∧ j.val < 2 * (n + 1)) := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    show (v.val % 2 ≠ j.val % 2 ∧ v.val < 2 * (n + 1) ∧ j.val < 2 * (n + 1)) ↔ _
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨fun h => h1 h.symm, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 h.symm, hv, h2⟩
  rw [hnb]
  -- Count the opposite-parity values by the explicit bijection with `Fin (n+1)`.
  have hcard : (Finset.univ.filter
      (fun j : Fin (2 * (n + 1) + 1) => j.val % 2 ≠ v.val % 2 ∧ j.val < 2 * (n + 1))).card
      = (Finset.univ : Finset (Fin (n + 1))).card := by
    refine Finset.card_nbij'
      (fun j => ⟨min (j.val / 2) n, by omega⟩)
      (fun b => ⟨2 * b.val + (v.val + 1) % 2, by have hb := b.isLt; omega⟩)
      ?_ ?_ ?_ ?_
    · intro j _
      simp
    · intro b _
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · show (2 * b.val + (v.val + 1) % 2) % 2 ≠ v.val % 2
        omega
      · show 2 * b.val + (v.val + 1) % 2 < 2 * (n + 1)
        have hb := b.isLt
        omega
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_filter] at hj
      obtain ⟨-, h1, h2⟩ := hj
      apply Fin.ext
      show 2 * min (j.val / 2) n + (v.val + 1) % 2 = j.val
      omega
    · intro b _
      apply Fin.ext
      show min ((2 * b.val + (v.val + 1) % 2) / 2) n = b.val
      have hb := b.isLt
      omega
  rw [hcard, Finset.card_univ, Fintype.card_fin]

/-- The edge count of `knnPlusW n` is `(n+1)²` (degree-sum formula: `2(n+1)` vertices of
degree `n+1` plus the isolated root). -/
private lemma knnPlusW_edgeFinset_card (n : ℕ) :
    (knnPlusW n).edgeFinset.card = (n + 1) ^ 2 := by
  have hlast : (knnPlusW n).degree (Fin.last (2 * (n + 1))) = 0 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero,
      Finset.eq_empty_iff_forall_notMem]
    intro j hj
    rw [SimpleGraph.mem_neighborFinset] at hj
    exact knnPlusW_last_isolated n j hj
  have hsum : ∑ w : Fin (2 * (n + 1) + 1), (knnPlusW n).degree w
      = 2 * (n + 1) * (n + 1) := by
    rw [Fin.sum_univ_castSucc]
    have hmid : ∀ i : Fin (2 * (n + 1)), (knnPlusW n).degree i.castSucc = n + 1 := by
      intro i
      exact knnPlusW_degree_lt n i.castSucc (by simp)
    simp only [hmid, hlast, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  have h2 : 2 * (knnPlusW n).edgeFinset.card = 2 * ((n + 1) * (n + 1)) := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges, hsum]
    ring
  have h3 := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h2
  rw [h3]
  ring

/-- The edge count of `knnPlusW n` is `(n+1)²` — hence its edge density is
`(n+1)/(2n+3)`, which tends to `1/2`.  Stated directly in the form the `ρ`-evaluation
needs (mirror the `TuranLimit` edge-density route; the underlying flag of
`mantelRootedSeq n` is the graph flag of `knnPlusW n`). -/
lemma mantelRootedSeq_underlying_edge_density_tendsto :
    Tendsto
      (fun n => (flagDensity₁ unlabelledEdgeFlag (unlabelSeq mantelRootedSeq n).2 : ℝ))
      atTop (𝓝 (1 / 2)) := by
  -- Two parts:
  -- (a) the count `e(knnPlusW n) = (n+1)²` (edges = pairs of distinct-parity vertices in
  --     the first `2(n+1)`; count via a product bijection evens × odds, or via
  --     `SimpleGraph.sum_degrees_eq_twice_card_edges` with degrees `n+1` for the `2(n+1)`
  --     bipartite vertices and `0` for the root);
  -- (b) the density `(n+1)²/C(2n+3, 2) = (n+1)/(2n+3) → 1/2` (mirror the §9.1/§9.2
  --     squeeze computations — `flagDensity_unlabelledEdge_eq` (C4Free) converts the flag
  --     density to `e(G)/C(N,2)`; then a real-limit computation).
  -- NOTE: if the exact name/shape of the unlabelled-edge flag differs (check
  -- `flagDensity_unlabelledEdge_eq` in `C4Free.lean` for the canonical form used across
  -- §9), ADAPT THE PROOF, NOT THE STATEMENT — if the statement's flag term is malformed,
  -- match it to the §9 canonical `unlabelledEdge` spelling (this statement may be
  -- adjusted ONLY to use the same canonical unlabelled-edge `FinFlag ∅ₜ` as `C4Free`).
  -- (a)+(b): each term is the concrete ratio `(n+1)/(2n+3)`.
  have hterm : ∀ n : ℕ,
      (flagDensity₁ unlabelledEdgeFlag (unlabelSeq mantelRootedSeq n).2 : ℝ)
        = ((n : ℝ) + 1) / (2 * (n : ℝ) + 3) := by
    intro n
    -- the underlying flag IS the graph flag of `knnPlusW n` (unlabelling forgets the root)
    show ((flagDensity₁ unlabelledEdgeFlag (graphFlag (knnPlusW n)) : ℚ) : ℝ)
        = ((n : ℝ) + 1) / (2 * (n : ℝ) + 3)
    have hchoose : (2 * (n + 1) + 1).choose 2 = (2 * n + 3) * (n + 1) := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel,
        show (2 * (n + 1) + 1) * (2 * (n + 1)) = 2 * ((2 * n + 3) * (n + 1)) by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [flagDensity_unlabelledEdge_eq, knnPlusW_edgeFinset_card, hchoose]
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [tendsto_congr hterm]
  -- `(n+1)/(2n+3) = 1/2 - 1/(2(2n+3)) → 1/2`.
  have hsplit : ∀ n : ℕ,
      ((n : ℝ) + 1) / (2 * (n : ℝ) + 3) = 1 / 2 - 1 / (2 * (2 * (n : ℝ) + 3)) := by
    intro n
    have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring
  rw [tendsto_congr hsplit]
  have hz : Tendsto (fun n : ℕ => 1 / (2 * (2 * (n : ℝ) + 3))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hfin := (tendsto_const_nhds (x := (1 / 2 : ℝ)) (f := (atTop : Filter ℕ))).sub hz
  simpa using hfin

/-! ## The planted witness and the strict inclusion -/

/-- The Mantel slice sits inside the constrained space `Q₀` of the triangle-free class. -/
lemma mantelSlice_subset_Q0 :
    mantelSlice ⊆ Qσ ((cliqueFreeClass 3).toHeredClass.constraintOf ∅ₜ).forb0 := by
  -- `mantelSlice = turanSlice 2 = eqSlice (constraintOf (cliqueFreeClass 3) ∅ₜ).forb0 ρ _`
  -- and `constraintOf gc σ = gc.toHeredClass.constraintOf σ` definitionally
  -- (GraphClassConstraint); an `eqSlice` is by definition a subset of its `Qσ`
  -- (see `eqSlice`/`posHomPoint_mem_eqSlice` in `CertificateSliceVanishing`).
  intro χ hχ
  exact hχ.1

/-- `ConvergesTo` is stable under composition with a strictly monotone index map (mirror of
the private helper in `RelativePlanted`). -/
private lemma convergesTo_comp_strictMono {n₀ : ℕ} {σ : FlagType (Fin n₀)}
    {s : FlagSeq σ} {a : FinFlag σ → ℝ} {ϕ : ℕ → ℕ} (hϕ : StrictMono ϕ)
    (h : ConvergesTo s a) : ConvergesTo (s ∘ ϕ) a :=
  ⟨h.1.comp hϕ, h.2.comp hϕ.tendsto_atTop⟩

/-- **The planted witness**: a `Y_Mantel`-planted view at the one-vertex type whose rooted
edge density is `0`. -/
theorem exists_mantel_planted_view_edge_zero :
    ∃ χ ∈ relQσ (cliqueFreeClass 3).toHeredClass mantelSlice vtype,
      (PositiveHomSpace.toPosHom χ) e = 0 := by
  -- Assembly (mirror the subsequence-extraction pattern of `exists_turan_limit` /
  -- `relQσ_Q0_eq`):
  -- 1. `mantelRootedSeq` has strictly increasing sizes (`Increases`).
  -- 2. Extract a rooted-profile-convergent subsequence
  --    (`increasing_flagSeq_contain_convergent_subseq` at `vtype`), and on it a further
  --    subsequence along which the UNDERLYING profiles (`unlabelSeq`) also converge.
  -- 3. `flagSeq_limit_mem_positiveHom` turns the two limits into homs; let `χ` be the
  --    rooted point (`posHomPoint` + roundtrip glue) and `φ` the underlying limit.
  -- 4. `χ ∈ relQσ`: the doubly-extracted `Gs` converges to `χ`'s profile; membership
  --    `underlyingMem` from `knnPlusW_cliqueFree` (via `underlyingMem_unlabel_mk`; the
  --    underlying graph of `knnPlusWLabeled` is `knnPlusW n`, and `cliqueFreeClass 3`
  --    membership IS `CliqueFree 3`); `unlabelSeq Gs` converges to `φ.coe`;
  --    `posHomPoint φ ∈ closure mantelSlice` via `subset_closure` +
  --    membership in `mantelSlice`: `posHomPoint φ ∈ Qσ …` by
  --    `flagSeqLimit_mem_Q0_of_underlyingMem`, and `φ ρ = 1/2` from
  --    `mantelRootedSeq_underlying_edge_density_tendsto` along the subsequence (the
  --    `ρ`-evaluation glue is the §9.2 `downwardNormalizingFactor_edge_eq_one` route —
  --    mirror how `exists_turan_limit` (TuranLimit, statements frozen) does it; then
  --    `posHomPoint_mem_eqSlice` to land in the slice).
  -- 5. `χ(e) = 0`: the `edgeFF`-coordinate of `χ`'s profile is the limit of the
  --    coordinates (`flagSeq_convergesTo_iff`), each `0` by
  --    `mantelRootedSeq_edge_density_zero`; convert `(toPosHom χ) e` to the coordinate
  --    via `PositiveHomSpace.toPosHom_basisVector` (`e = ⟦basisVector edgeFF⟧`).
  classical
  -- 1. strictly increasing sizes
  have hinc : Increases mantelRootedSeq := by
    apply increases_of_consecutive_lt
    intro k
    show 2 * (k + 1) + 1 < 2 * (k + 1 + 1) + 1
    omega
  -- 2. extract a rooted-profile-convergent subsequence, then a further subsequence along
  --    which the underlying (unlabelled) profiles also converge
  obtain ⟨a, ϕ₁, hϕ₁, hconv₁⟩ :=
    increasing_flagSeq_contain_convergent_subseq mantelRootedSeq hinc
  obtain ⟨b, ϕ₂, hϕ₂, hconv₂⟩ :=
    increasing_flagSeq_contain_convergent_subseq (unlabelSeq (mantelRootedSeq ∘ ϕ₁)) hconv₁.1
  set Gs : FlagSeq vtype := (mantelRootedSeq ∘ ϕ₁) ∘ ϕ₂ with hGsdef
  have hconvGs : ConvergesTo Gs (a : FinFlag vtype → ℝ) :=
    convergesTo_comp_strictMono hϕ₂ hconv₁
  have hconv0 : ConvergesTo (unlabelSeq Gs) (b : FinFlag ∅ₜ → ℝ) := hconv₂
  -- 3. the two limit homomorphisms
  obtain ⟨χhom, hχcoe⟩ := flagSeq_limit_mem_positiveHom Gs hconvGs
  obtain ⟨φ, hφcoe⟩ := flagSeq_limit_mem_positiveHom (unlabelSeq Gs) hconv0
  -- 4a. every term's underlying graph is triangle-free
  have hmem : ∀ t, (cliqueFreeClass 3).toHeredClass.underlyingMem (unlabel (Gs t).2) := by
    intro t
    show (cliqueFreeClass 3).toHeredClass.underlyingMem
      (unlabel (⟦knnPlusWLabeled (ϕ₁ (ϕ₂ t))⟧ : Flag vtype (Fin (2 * (ϕ₁ (ϕ₂ t) + 1) + 1))))
    rw [HeredClass.underlyingMem_unlabel_mk]
    exact knnPlusW_cliqueFree (ϕ₁ (ϕ₂ t))
  -- 4b. the base limit is a constrained limit …
  have hmemQ0 : posHomPoint φ ∈ Qσ ((cliqueFreeClass 3).toHeredClass.constraintOf ∅ₜ).forb0 := by
    refine flagSeqLimit_mem_Q0_of_underlyingMem (cliqueFreeClass 3).toHeredClass
      (sH := unlabelSeq Gs) ?_ ?_
    · rw [hφcoe]; exact hconv0
    · intro t; exact hmem t
  -- 4c. … of edge density `φ ρ = 1/2` (the §9.2 `ρ`-evaluation glue)
  have hρval : φ ρ = 1 / 2 := by
    have hedgeunlabel : (⟨edgeFF.1, unlabel edgeFF.2⟩ : FinFlag ∅ₜ) = ⟨2, unlabelledEdgeFlag⟩ :=
      rfl
    have hρ : φ ρ
        = (downwardNormalizingFactor edgeFF.2 : ℝ) * φ.coe ⟨2, unlabelledEdgeFlag⟩ := by
      show φ (downward e) = _
      rw [e, downward_basisVector, PositiveHom.map_smul, hedgeunlabel, ← PositiveHom.coe_flag]
    rw [downwardNormalizingFactor_edge_eq_one] at hρ
    have hpt := (flagSeq_convergesTo_iff.mp hconv0).2 ⟨2, unlabelledEdgeFlag⟩
    have hhalf : Tendsto (fun t => flagDensitySeq (unlabelSeq Gs) t ⟨2, unlabelledEdgeFlag⟩)
        atTop (𝓝 (1 / 2)) :=
      mantelRootedSeq_underlying_edge_density_tendsto.comp (hϕ₁.comp hϕ₂).tendsto_atTop
    have hlim := tendsto_nhds_unique hpt hhalf
    rw [hρ, hφcoe, Rat.cast_one, one_mul]
    exact hlim
  -- 4d. hence the base limit lies in the Mantel slice
  have hslice : posHomPoint φ ∈ mantelSlice := by
    have h2 : posHomPoint φ ∈ Qσ (constraintOf (cliqueFreeClass (2 + 1)) ∅ₜ).forb0 ∧
        φ ρ = (((2 : ℕ) : ℝ) - 1) / ((2 : ℕ) : ℝ) := by
      refine ⟨hmemQ0, ?_⟩
      rw [hρval]; norm_num
    exact posHomPoint_mem_eqSlice.mpr h2
  -- 5. assemble the planted view and its vanishing rooted edge density
  refine ⟨posHomPoint χhom, ?_, ?_⟩
  · simp only [relQσ, Set.mem_setOf_eq]
    refine ⟨Gs, φ, ?_, hmem, ?_, subset_closure hslice⟩
    · show ConvergesTo Gs (PositiveHomSpace.toPosHom (posHomPoint χhom)).coe
      rw [toPosHom_posHomPoint, hχcoe]
      exact hconvGs
    · show ConvergesTo (unlabelSeq Gs) φ.coe
      rw [hφcoe]
      exact hconv0
  · -- the `edgeFF`-coordinate of the profile is the limit of the constant-`0` densities
    have hval : (PositiveHomSpace.toPosHom (posHomPoint χhom)) e
        = (a : FinFlag vtype → ℝ) edgeFF := by
      show (PositiveHomSpace.toPosHom (posHomPoint χhom)) ⟦basisVector edgeFF⟧ = _
      rw [PositiveHomSpace.toPosHom_basisVector, posHomPoint_val_apply,
        ← PositiveHom.coe_flag, hχcoe]
    rw [hval]
    have hzero : ∀ t, flagDensitySeq Gs t edgeFF = 0 := by
      intro t
      show (flagDensity₁ edgeFF.2 (mantelRootedSeq (ϕ₁ (ϕ₂ t))).2 : ℝ) = 0
      rw [mantelRootedSeq_edge_density_zero]
      norm_num
    have hpt := (flagSeq_convergesTo_iff.mp hconvGs).2 edgeFF
    have h0 : Tendsto (fun t => flagDensitySeq Gs t edgeFF) atTop (𝓝 0) := by
      simp only [hzero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hpt h0

/-- **Slices break root-plantability: the Mantel slice** (`prop:mantel-not-plantable`):
`S_vtype(Y_Mantel) ⊊ Q_vtype(Y_Mantel)`.

`hpin` is `thm:relative-mantel` (i) — the relative support pins the rooted edge density to
`1/2` — taken as an explicit hypothesis (classical input: Erdős–Simonovits uniqueness of
the Mantel-extremal limit + the Dirac extension of the bipartite graphon; README
deviation).  Contrast: the triangle-free class itself IS root-plantable at every type
(`clique_free_root_plantable`, §5). -/
theorem mantel_not_relatively_plantable
    (hpin : ∀ ψ ∈ relSσ mantelSlice vtype, (PositiveHomSpace.toPosHom ψ) e = 1 / 2) :
    relSσ mantelSlice vtype ⊂ relQσ (cliqueFreeClass 3).toHeredClass mantelSlice vtype := by
  -- `ssubset_iff_of_subset` with `relSσ_subset_relQσ _ mantelSlice_subset_Q0`; the witness
  -- `χ` of `exists_mantel_planted_view_edge_zero` is in `relQσ` but cannot be in `relSσ`
  -- (`hpin` would force `χ(e) = 1/2 ≠ 0` — `norm_num`).
  obtain ⟨χ, hχQ, hχe⟩ := exists_mantel_planted_view_edge_zero
  rw [Set.ssubset_iff_of_subset
    (relSσ_subset_relQσ (cliqueFreeClass 3).toHeredClass mantelSlice_subset_Q0)]
  refine ⟨χ, hχQ, fun hχS => ?_⟩
  have h := hpin χ hχS
  rw [hχe] at h
  norm_num at h

end FlagAlgebras.MetaTheory
