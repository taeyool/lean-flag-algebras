import LeanFlagAlgebras.ErdosPentagon.Lemmas

/-! # The Erdős pentagon problem

The headline file: the maximum 5-cycle density among triangle-free graphs.
Combines the flag-algebra upper bound from `Lemmas.lean` with an explicit
blow-up lower-bound construction to prove:

* `ErdosPentagon_Turan_upperBound` — `generalizedTuranDensity K3 C5 ≤ 24/625`;
* `ErdosPentagon_Turan_lowerBound` — `generalizedTuranDensity K3 C5 ≥ 24/625`,
  via the triangle-free `n`-fold blow-up of `C5`;
* `ErdosPentagon_Turan : generalizedTuranDensity K3 C5 = 24 / 625` — the
  solution of the Erdős pentagon problem. -/

open FlagAlgebras GraphAlgebras Forbid
open Filter Topology SimpleGraph

namespace ErdosPentagonAPI

/-- Upper bound: the `K₃`-free generalized Turán density of the pentagon is at
most `24/625`, transferred from the flag-algebra bound
`ErdosPentagon_flagAlgebra`. -/
theorem ErdosPentagon_Turan_upperBound
    : generalizedTuranDensity K3 C5 ≤ 24 / 625
  :=
  generalizedTuranDensity_le_of_forbidLE (by norm_num)
    (inducedForbidLE_toFinFlag_imp_forbidLE K3 ErdosPentagon_flagAlgebra)

/-- The `n`-fold blow-up of `G`: each vertex is replaced by an independent set
of `n` copies, with edges inherited from `G` on the first coordinate. -/
def blowUp
    {V : Type} [Fintype V] (G : SimpleGraph V) (n : ℕ)
    : SimpleGraph (V × Fin n)
  := {
    Adj v w := G.Adj v.1 w.1
    symm v w := by apply G.symm
  }

/-- Adjacency in the blow-up reduces to adjacency in `G` on first coordinates. -/
theorem blowUp_adj_iff
    {V : Type} [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (v w : V × Fin n)
    : (blowUp G n).Adj v w ↔ G.Adj v.1 w.1
  := by
  simp only [blowUp]

/-- Blowing up preserves triangle-freeness: if `G` is `K₃`-free then so is its
blow-up. -/
theorem blowUp_K3_free
    {m : ℕ} {G : SimpleGraph (Fin m)}
    (n : ℕ) (hfree : K3.Free G)
    : K3.Free (blowUp G n)
  := by
  contrapose hfree
  rcases hfree with ⟨C⟩
  apply Nonempty.intro
  exact {
    toHom := {
      toFun := fun i => (C i).1
      map_rel' := by
        intro i j hAdj
        rw [← blowUp_adj_iff]
        exact C.toHom.map_rel' hAdj
    }
    injective' := by
      intro i j hij
      by_contra hne
      have hK3 : K3.Adj i j := by simpa [K3] using hne
      have hBlow : (blowUp G n).Adj (C i) (C j) := C.toHom.map_rel' hK3
      have hGadj : G.Adj (C i).1 (C j).1 := (blowUp_adj_iff G n (C i) (C j)).1 hBlow
      have hij' : (C i).1 = (C j).1 := by simpa using hij
      exact (G.loopless (C i).1) (by simp [hij'] at hGadj)
  }

/-- `F`-freeness transfers across a graph isomorphism. -/
theorem free_of_iso
    {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    {F : SimpleGraph U} {G : SimpleGraph V} {G' : SimpleGraph W}
    (h_iso : G ≃g G') (hfree : F.Free G)
    : F.Free G'
  := by
  contrapose hfree
  rcases hfree with ⟨C⟩
  refine ⟨SimpleGraph.Copy.mk (h_iso.symm.toHom.comp C.toHom) ?_⟩
  intro i j hij
  apply C.injective'
  apply h_iso.symm.injective
  simpa using hij

lemma fin_div_lt
    {m n : ℕ} (i : Fin (m * n))
    : i / n < m
  := by
  apply Nat.div_lt_of_lt_mul
  simp_rw [Nat.mul_comm]
  exact i.isLt

/-- `Fin`-indexed variant of `blowUp`: the `n`-fold blow-up of a graph on
`Fin m`, realised on `Fin (m * n)`. -/
def blowUp_fin
    {m : ℕ} (G : SimpleGraph (Fin m)) (n : ℕ)
    : SimpleGraph (Fin (m * n))
  := {
    Adj i j := G.Adj i.divNat j.divNat
    symm i j := by
      intro h
      exact G.symm h
  }

/-- The two blow-up constructions are isomorphic. -/
def blowUp_fin_iso
    {m : ℕ} (G : SimpleGraph (Fin m)) (n : ℕ)
    : blowUp_fin G n ≃g blowUp G n
  := {
    toEquiv := (finProdFinEquiv (m := m) (n := n)).symm
    map_rel_iff' := by
      intro i j
      simp [blowUp_fin, blowUp_adj_iff]
  }

set_option maxHeartbeats 0 in
lemma K3_free_C5
    : K3.Free C5
  := by
  intro hcont
  rcases hcont with ⟨f⟩
  have h01 : C5.Adj (f 0) (f 1) := f.toHom.map_adj (by simp [K3])
  have h12 : C5.Adj (f 1) (f 2) := f.toHom.map_adj (by simp [K3])
  have h20 : C5.Adj (f 2) (f 0) := f.toHom.map_adj (by simp [K3])
  have hne01 : f 0 ≠ f 1 := by
    intro h
    have : (0 : Fin 3) = 1 := f.injective h
    contradiction
  have hne12 : f 1 ≠ f 2 := by
    intro h
    have : (1 : Fin 3) = 2 := f.injective h
    contradiction
  have hne20 : f 2 ≠ f 0 := by
    intro h
    have : (2 : Fin 3) = 0 := f.injective h
    contradiction
  generalize ha : f 0 = a at h01 h20 hne01 hne20
  generalize hb : f 1 = b at h01 h12 hne01 hne12
  generalize hc : f 2 = c at h12 h20 hne12 hne20
  fin_cases a <;>
  fin_cases b <;>
  fin_cases c <;>
  simp [C5] at h01 h12 h20 hne01 hne12 hne20

/-- The `n`-fold blow-up of `C5` contains at least `n^5` copies of `C5` (one
per choice of a representative in each of the five blown-up classes). -/
lemma subgraphCount_blowUp_C5_ge
    (n : ℕ)
    : subgraphCount C5 (blowUp C5 n) ≥ n ^ 5
  := by
  dsimp [subgraphCount, subgraphSet]
  let f : (Fin 5 → Fin n) ↪ (blowUp C5 n).Subgraph := {
    toFun g :=
      let ϕ : Fin 5 ↪ Fin 5 × Fin n := {
        toFun i := (i, g i)
        inj' := by
          intro i j hij
          simp_all only [Prod.mk.injEq]
      }
      (⊤ : (blowUp C5 n).Subgraph).induce (Finset.univ.map ϕ)
    inj' := by
      intro g g' hgg'
      ext i
      simp at hgg'
      have hmem : (i, g i) ∈ ((⊤ : (blowUp C5 n).Subgraph).induce
          (Set.range (fun j ↦ (j, g' j)))).verts := by
        simp [← hgg']
      have hi : g' i = g i := by
        simpa [Subgraph.induce_verts] using hmem
      simpa using congrArg Fin.val hi.symm
  }
  let S : Set (blowUp C5 n).Subgraph := (Set.univ : Set (Fin 5 → Fin n)).toFinset.map f
  have hS_card : S.toFinset.card = n ^ 5 := by simp [S]
  rw [← hS_card]
  apply Finset.card_le_card
  apply Set.toFinset_mono
  intro H hH
  simp [S] at hH
  rcases hH with ⟨g, hg⟩
  subst hg
  constructor
  · simp [f]
  · exact Nonempty.intro {
      toEquiv := {
        toFun := fun v => v.1.1
        invFun := fun i => ⟨(i, g i), by simp [f]⟩
        left_inv := by
          intro v
          rcases v with ⟨⟨i, x⟩, hx⟩
          have hx' : ∃ y, (y, g y) = (i, x) := by
            simpa [f] using hx
          rcases hx' with ⟨j, hj⟩
          have hj1 : j = i := by simpa using congrArg Prod.fst hj
          have hj2 : g j = x := by simpa using congrArg Prod.snd hj
          have hxg : x = g i := by simpa [hj1] using hj2.symm
          apply Subtype.ext
          simp [hxg]
        right_inv := by
          intro i
          rfl
      }
      map_rel_iff' := by
        intro u v
        have hu' : ∃ y, (y, g y) = u.1 := by
          simpa [f] using u.2
        have hv' : ∃ y, (y, g y) = v.1 := by
          simpa [f] using v.2
        constructor
        · intro huv
          have : (∃ y, (y, g y) = u.1) ∧ (∃ y, (y, g y) = v.1) ∧ C5.Adj u.1.1 v.1.1 :=
            ⟨hu', hv', huv⟩
          simpa [f, Subgraph.coe, Subgraph.induce_adj, Subgraph.top_adj, blowUp_adj_iff] using this
        · intro huv
          have huv' : (∃ y, (y, g y) = u.1) ∧ (∃ y, (y, g y) = v.1) ∧ C5.Adj u.1.1 v.1.1 := by
            simpa [f, Subgraph.coe, Subgraph.induce_adj, Subgraph.top_adj, blowUp_adj_iff] using huv
          exact huv'.2.2
    }

/-- Lower bound on the generalized extremal number: the triangle-free blow-up
`blowUp_fin C5 n` on `5n` vertices already realises `≥ n^5` pentagons. -/
theorem generalizedExtremalNumber_K3_C5_ge
    (n : ℕ)
    : generalizedExtremalNumber (5 * n) K3 C5 ≥ n ^ 5
  := by
  suffices hWit : ∃ G : SimpleGraph (Fin (5 * n)), K3.Free G ∧ n ^ 5 ≤ GraphAlgebras.subgraphCount C5 G by
    rcases hWit with ⟨G, hGfree, hGcount⟩
    refine le_trans hGcount (Finset.le_sup ?_)
    simpa [Finset.mem_filter] using hGfree
  use blowUp_fin C5 n
  constructor
  · apply free_of_iso (blowUp_fin_iso C5 n).symm
    exact blowUp_K3_free n K3_free_C5
  · rw [subgraphCount_eq_of_iso C5 (blowUp_fin_iso C5 n)]
    exact subgraphCount_blowUp_C5_ge n

/-- Normalised lower bound: the blow-up construction gives pentagon density
`≥ 24/625` along the subsequence of orders `5n`. -/
theorem generalizedExtremalNumber_K3_C5_div_choose_ge
    (n : ℕ) (hn : 0 < n)
    : (generalizedExtremalNumber (5 * n) K3 C5 / (5 * n).choose 5 : ℝ) ≥ 24 / 625
  := by
  have hchoose_pos : (0 : ℝ) < (5 * n).choose 5 :=
    Nat.cast_pos'.mpr (Nat.choose_pos (by nlinarith [hn]))
  calc
    generalizedExtremalNumber (5 * n) K3 C5 / (5 * n).choose 5
        ≥ (n : ℝ) ^ 5 / (5 * n).choose 5 := by
      field_simp
      exact_mod_cast (generalizedExtremalNumber_K3_C5_ge n)
    _ ≥ (n : ℝ) ^ 5 / (((5 * n) ^ 5) / Nat.factorial 5 : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) hchoose_pos
      apply le_trans (Nat.choose_le_pow_div (α := ℝ) 5 (5 * n))
      simp only [Nat.cast_mul, Nat.cast_ofNat, le_refl]
    _ = (24 / 625 : ℝ) := by
      field_simp
      norm_num

/-- Lower bound: the `K₃`-free generalized Turán density of the pentagon is at
least `24/625`, taking the limit of the blow-up construction. -/
theorem ErdosPentagon_Turan_lowerBound
    : generalizedTuranDensity K3 C5 ≥ 24 / 625
  := by
  let f : ℕ → ℝ := fun n ↦ (generalizedExtremalNumber n K3 C5 / n.choose 5 : ℝ)
  let g : ℕ → ℝ := fun n ↦ f (5 * (n + 1))
  have hf : Tendsto f atTop (𝓝 (generalizedTuranDensity K3 C5)) := by
    simpa [f] using (tendsto_generalizedTuranDensity K3 C5)
  have hmul_mono : StrictMono (fun n : ℕ ↦ 5 * (n + 1)) := by
    intro a b hab
    exact Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right hab 1) (by decide : 0 < 5)
  have hg : Tendsto g atTop (𝓝 (generalizedTuranDensity K3 C5)) :=
    hf.comp (StrictMono.tendsto_atTop hmul_mono)
  refine le_of_tendsto_of_tendsto'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (24 / 625 : ℝ)) atTop (𝓝 (24 / 625 : ℝ)))
    hg ?_
  intro n
  simpa [g, f, ge_iff_le] using
    (generalizedExtremalNumber_K3_C5_div_choose_ge (n + 1) (Nat.succ_pos n))

/-- **Solution of the Erdős pentagon problem.** The maximum density of the
5-cycle among triangle-free graphs is exactly `24/625`:
`generalizedTuranDensity K3 C5 = 24 / 625`. -/
theorem ErdosPentagon_Turan
    : generalizedTuranDensity K3 C5 = 24 / 625
  := by
  apply le_antisymm
  · exact ErdosPentagon_Turan_upperBound
  · exact ErdosPentagon_Turan_lowerBound

end ErdosPentagonAPI
