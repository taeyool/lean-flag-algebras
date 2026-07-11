import LeanFlagAlgebras.MetaTheory.GraphonRootedMeasure
import LeanFlagAlgebras.MetaTheory.ParametricP4Slice
import LeanFlagAlgebras.MetaTheory.GraphonRigidity

/-! # From slice identities to kernel equations

The capstone of the rooted transport: rooted flag identities holding on the relative support
of the `K₄`-free `P₄`-slice become **almost-everywhere kernel equations** for any graphon
whose `φ_W` lies in the slice — exactly the hypotheses of `Graphon.r3_rigidity`.  This is the
Lean form of the paper's rooted dictionary (`paper.tex:4861–4875`): at an ordered edge root
`(x, y)`, `a_τ = d(x) − c(x,y)`, `b_τ = d(y) − c(x,y)`, `g_τ = c(x,y)`; at an ordered non-edge
root, `z_η = 1 − d(x) − d(y) + c(x,y)`, `g_η = c(x,y)`.

* `graphonRootedHom_a_tau` / `_b_tau` / `_g_tau` / `_z_eta` / `_g_eta` — the **kernel
  dictionary**: the rooted conditional homomorphism's values on the generated three-vertex
  flags are the deg/codeg expressions above (single-graph fibres at `n = 3`; the root-pair
  factor cancels against the profile's conditioning).
* `k4freeP4_graphon_Rtau_eq_zero` / `k4freeP4_graphon_Reta_eq_zero` — the transport: the
  slice equations (`k4freeP4_tau_equation`/`_tau_symm`/`_eta_equation`,
  `ParametricP4Slice.lean`) hold on `relSσ k4freeP4Slice`, hence
  `ℙ[φ_W]`-a.e. (`support_subset_relSσ` + `Measure.support_mem_ae`), hence — through
  `rootedViewMeasure_eq_extend` and the pushforward — for `rootWeight`-a.e. pair `(u, v)`;
  with the dictionary this is exactly the right-hand side of
  `Rtau_eq_zero_iff_ae`/`Reta_eq_zero_iff_ae` (`GraphonMoments.lean`).
* `k4freeP4_graphon_tripartite` — the assembled `r3_rigidity` conclusion: any graphon whose
  `φ_W` lies in the `K₄`-free `P₄`-slice (and has both root types admissible in mass) is
  a.e. the balanced complete tripartite graphon.

The hypothesis `posHomPoint (graphonHom W) ∈ k4freeP4Slice` is purely algebraic
(`mem_Qσ_iff`: `φ_W` vanishes on the forbidden `K₄` flags, plus the `P₄`-density evaluation) —
no graph-limit existential enters.  The transport theorems are **Tier-2** (they consume the
certificate-derived slice equations); the dictionary lemmas themselves are Tier-1.
-/

open MeasureTheory unitInterval Finset
open scoped Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras
open CompleteGraphFreeP4

/-! ## The kernel dictionary: shared engine

All five dictionary lemmas share one scheme: identify the (unique) standard-rooted graph
`G : SimpleGraph (Fin 3)` witnessing the generated flag, split `unnormRootedDensity` into the
root-pair factor times an integral of the two third-vertex factors, and evaluate that integral
in closed form.  The private lemmas below assemble this engine; only the five case-specific
witnesses (`G_atau`, …) and their matching facts about the generated `Sym2LabeledGraph`s differ. -/

/-- On a probability space, a measurable function squeezed between two constants is
integrable (local copy of the workhorse used throughout `MetaTheory/`). -/
private lemma integrable_of_bounds'' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {a b : ℝ} (hf : Measurable f)
    (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) : Integrable f μ :=
  integrable_of_le_of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall ha) (Filter.Eventually.of_forall hb)
    (integrable_const a) (integrable_const b)

/-- Marginalisation: the integral over `Fin 3 → I` of a function of the third coordinate alone
is the integral of that function over `I` (via `MeasurableEquiv.piFinSuccAbove` splitting off
index `2`, then `Fubini` collapses the complementary probability factor to `1`). -/
private lemma integral_eval_two (F : I → ℝ) (hF : Measurable F) (hF0 : ∀ w, 0 ≤ F w)
    (hF1 : ∀ w, F w ≤ 1) :
    ∫ y : Fin 3 → I, F (y 2) = ∫ w : I, F w := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => I) 2
  have hcomp := hmp.integral_comp' (fun z : I × (Fin 2 → I) => F z.1)
  have hLHS : (fun x : Fin 3 → I =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => I) 2 x).1))
      = (fun x : Fin 3 → I => F (x 2)) := by
    funext x
    rfl
  rw [hLHS] at hcomp
  rw [hcomp]
  have hInt : Integrable (fun z : I × (Fin 2 → I) => F z.1) volume :=
    integrable_of_bounds'' (hF.comp measurable_fst) (fun z => hF0 z.1) (fun z => hF1 z.1)
  rw [show (volume : Measure (I × (Fin 2 → I)))
      = (volume : Measure I).prod (volume : Measure (Fin 2 → I)) from rfl,
    integral_prod _ hInt]
  simp

/-- `FlagType_2_1.Adj 0 1` holds (the `τ` type is an edge; local re-derivation of the private
idiom used in `TuranSliceIdentities.lean`/`TuranAut.lean`). -/
private lemma tau_adj01 : FlagType_2_1.Adj 0 1 :=
  (FlagAlgebras.Compute.Sym2FlagType.toFlagType_adj_iff Sym2FlagType_2_1 0 1).mpr (by decide)

/-- `¬ FlagType_2_0.Adj 0 1` (the `η` type is a non-edge). -/
private lemma eta_not_adj01 : ¬ FlagType_2_0.Adj 0 1 := fun h =>
  absurd ((FlagAlgebras.Compute.Sym2FlagType.toFlagType_adj_iff Sym2FlagType_2_0 0 1).mp h)
    (by decide)

/-- A three-vertex graph given directly by its adjacency pattern on the pairs `01, 02, 12`
(each a `Bool`), avoiding `Finset`/`Set` membership decidability issues under
`open scoped Classical` (which shadows the computable `Decidable` instances `decide` needs). -/
private def mkG3 (b01 b02 b12 : Bool) : SimpleGraph (Fin 3) where
  Adj a b :=
    (a = 0 ∧ b = 1 ∧ b01) ∨ (a = 1 ∧ b = 0 ∧ b01) ∨
    (a = 0 ∧ b = 2 ∧ b02) ∨ (a = 2 ∧ b = 0 ∧ b02) ∨
    (a = 1 ∧ b = 2 ∧ b12) ∨ (a = 2 ∧ b = 1 ∧ b12)
  symm := by
    intro a b h
    rcases h with h|h|h|h|h|h <;> tauto
  loopless := by
    intro a h
    rcases h with ⟨h1,h2,_⟩|⟨h1,h2,_⟩|⟨h1,h2,_⟩|⟨h1,h2,_⟩|⟨h1,h2,_⟩|⟨h1,h2,_⟩ <;> subst h1 <;>
      simp_all

/-- Two three-vertex graphs agree once they agree, after transport by `ψ`, on the three
increasing pairs (the finite case-bash behind every existence witness below). -/
private lemma graph3_iso_ext {G H : SimpleGraph (Fin 3)} (ψ : Fin 3 ≃ Fin 3)
    (h01 : H.Adj (ψ 0) (ψ 1) ↔ G.Adj 0 1) (h02 : H.Adj (ψ 0) (ψ 2) ↔ G.Adj 0 2)
    (h12 : H.Adj (ψ 1) (ψ 2) ↔ G.Adj 1 2) :
    ∀ a b : Fin 3, H.Adj (ψ a) (ψ b) ↔ G.Adj a b := by
  intro a b
  fin_cases a <;> fin_cases b
  · simp
  · exact h01
  · exact h02
  · rw [H.adj_comm, G.adj_comm]; exact h01
  · simp
  · exact h12
  · rw [H.adj_comm, G.adj_comm]; exact h02
  · rw [H.adj_comm, G.adj_comm]; exact h12
  · simp

/-- The general existence engine: `G` (root-compatible) is standard-rooted-flag-equal to `H`
once a graph iso `ψ` carrying `G`'s pairs to `H`'s (via `graph3_iso_ext`) also carries the
roots to `H`'s type embedding. -/
private lemma mkStdRooted_eq_of_iso {σ' : FlagType (Fin 2)} (hn : (2:ℕ) ≤ 3)
    {G : SimpleGraph (Fin 3)} (h : RootCompatible σ' hn G)
    (H : LabeledGraph σ' (Fin 3)) (ψ : Fin 3 ≃ Fin 3)
    (hiso : ∀ a b : Fin 3, H.graph.Adj (ψ a) (ψ b) ↔ G.Adj a b)
    (hψ0 : ψ (Fin.castLE hn (0:Fin 2)) = H.type_embed 0)
    (hψ1 : ψ (Fin.castLE hn (1:Fin 2)) = H.type_embed 1) :
    (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin 3)) = ⟦H⟧ := by
  apply flagEqv.sound
  refine ⟨⟨ψ, fun {a b} => hiso a b⟩, ?_⟩
  funext a
  show ψ ((mkStdRooted σ' hn G h).type_embed a) = H.type_embed a
  rw [mkStdRooted_type_embed_apply]
  fin_cases a
  · exact hψ0
  · exact hψ1

/-- The filter picking out the standard-rooted representatives of a flag class on `Fin 3` is a
singleton, given one witness: any other root-compatible witness is flag-equal to it via
`mkStdRooted_flag_eq_iff`, whose root-fixing iso of `Fin 3` is forced to be the identity
(fixing two of the three points forces the third). -/
private lemma stdRooted_filter_singleton {σ' : FlagType (Fin 2)} (hn : (2:ℕ) ≤ 3)
    {G : SimpleGraph (Fin 3)} (h : RootCompatible σ' hn G)
    {F : Flag σ' (Fin 3)} (hGF : (⟦mkStdRooted σ' hn G h⟧ : Flag σ' (Fin 3)) = F) :
    (Finset.univ.filter (fun G' : SimpleGraph (Fin 3) =>
        ∃ h' : RootCompatible σ' hn G', (⟦mkStdRooted σ' hn G' h'⟧ : Flag σ' (Fin 3)) = F))
      = {G} := by
  ext G'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h', hG'F⟩
    have heq : (⟦mkStdRooted σ' hn G' h'⟧ : Flag σ' (Fin 3)) = ⟦mkStdRooted σ' hn G h⟧ := by
      rw [hG'F, hGF]
    obtain ⟨ψ, hψ⟩ := (mkStdRooted_flag_eq_iff hn G' G h' h).mp heq
    have h0 : ψ 0 = 0 := by simpa using hψ 0
    have h1 : ψ 1 = 1 := by simpa using hψ 1
    have hψ2 : ψ 2 = 2 := by
      have hne0 : ψ 2 ≠ 0 := fun he => by
        have := ψ.toEquiv.injective (he.trans h0.symm); exact absurd this (by decide)
      have hne1 : ψ 2 ≠ 1 := fun he => by
        have := ψ.toEquiv.injective (he.trans h1.symm); exact absurd this (by decide)
      omega
    have hψid : ∀ x : Fin 3, ψ x = x := by
      intro x; fin_cases x
      · exact h0
      · exact h1
      · exact hψ2
    ext a b
    have hthis := ψ.map_rel_iff' (a := a) (b := b)
    rw [show ψ.toEquiv a = a from hψid a, show ψ.toEquiv b = b from hψid b] at hthis
    exact hthis.symm
  · rintro rfl
    exact ⟨h, hGF⟩

private lemma belowDiagPairs_three :
    belowDiagPairs 3 = {((0:Fin 3),(1:Fin 3)), ((0:Fin 3),(2:Fin 3)), ((1:Fin 3),(2:Fin 3))} := by
  ext p
  obtain ⟨p1,p2⟩ := p
  fin_cases p1 <;> fin_cases p2 <;> simp [mem_belowDiagPairs]

/-- **The shared value engine**: for ANY three-vertex graph `G`, `unnormRootedDensity` splits
into the constant root-pair factor times an integral of the two third-vertex factors. -/
private lemma unnormRootedDensity_pattern (G : SimpleGraph (Fin 3)) (hn : (2:ℕ) ≤ 3)
    (W : Graphon) (u v : I) :
    unnormRootedDensity W hn G u v
      = adjWeight W (G.Adj 0 1) u v
        * ∫ w : I, adjWeight W (G.Adj 0 2) u w * adjWeight W (G.Adj 1 2) v w := by
  have hpt : ∀ y : Fin 3 → I,
      inducedWeight W G (pinRoots hn u v y)
        = adjWeight W (G.Adj 0 1) u v
          * (adjWeight W (G.Adj 0 2) u (y 2) * adjWeight W (G.Adj 1 2) v (y 2)) := by
    intro y
    unfold inducedWeight
    rw [belowDiagPairs_three]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    have hp0 : pinRoots hn u v y 0 = u := by simpa using pinRoots_apply_root0 hn u v y
    have hp1 : pinRoots hn u v y 1 = v := by simpa using pinRoots_apply_root1 hn u v y
    have hc0 : Fin.castLE hn (0:Fin 2) = (0:Fin 3) := rfl
    have hc1 : Fin.castLE hn (1:Fin 2) = (1:Fin 3) := rfl
    have hp2 : pinRoots hn u v y 2 = y 2 :=
      pinRoots_apply_of_ne hn u v y (hc0 ▸ (by decide : (2:Fin 3) ≠ 0))
        (hc1 ▸ (by decide : (2:Fin 3) ≠ 1))
    dsimp only
    rw [hp0, hp1, hp2]
  unfold unnormRootedDensity
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const_mul]
  congr 1
  have hmeasU : Measurable (fun w => adjWeight W (G.Adj 0 2) u w) := by
    unfold adjWeight; split_ifs
    · exact W.measurable_left u
    · exact measurable_const.sub (W.measurable_left u)
  have hmeasV : Measurable (fun w => adjWeight W (G.Adj 1 2) v w) := by
    unfold adjWeight; split_ifs
    · exact W.measurable_left v
    · exact measurable_const.sub (W.measurable_left v)
  exact integral_eval_two _ (hmeasU.mul hmeasV)
    (fun w => mul_nonneg (adjWeight_nonneg W _ u w) (adjWeight_nonneg W _ v w))
    (fun w => mul_le_one₀ (adjWeight_le_one W _ u w) (adjWeight_nonneg W _ v w)
      (adjWeight_le_one W _ v w))

private lemma integrable_W_left (W : Graphon) (x : I) : Integrable (fun w => W.W x w) :=
  integrable_of_bounds'' (W.measurable_left x) (fun w => W.nonneg x w) (fun w => W.le_one x w)

private lemma integrable_W_mul (W : Graphon) (x y : I) :
    Integrable (fun w => W.W x w * W.W y w) :=
  integrable_of_bounds'' (a := 0) (b := 1) ((W.measurable_left x).mul (W.measurable_left y))
    (fun w => mul_nonneg (W.nonneg x w) (W.nonneg y w))
    (fun w => by nlinarith [W.nonneg x w, W.le_one x w, W.nonneg y w, W.le_one y w])

/-- Both-adjacent pattern: `∫ W(u,·)·W(v,·) = codeg u v`. -/
private lemma integral_adjWeight_TT {P Q : Prop} (hP : P) (hQ : Q) (W : Graphon) (u v : I) :
    ∫ w : I, adjWeight W P u w * adjWeight W Q v w = W.codeg u v := by
  have e : (fun w => adjWeight W P u w * adjWeight W Q v w) = fun w => W.W u w * W.W v w := by
    funext w; unfold adjWeight; rw [if_pos hP, if_pos hQ]
  rw [e]; rfl

/-- First-only pattern: `∫ W(u,·)·(1-W(v,·)) = deg u - codeg u v`. -/
private lemma integral_adjWeight_TF {P Q : Prop} (hP : P) (hQ : ¬ Q) (W : Graphon) (u v : I) :
    ∫ w : I, adjWeight W P u w * adjWeight W Q v w = W.deg u - W.codeg u v := by
  have e : (fun w => adjWeight W P u w * adjWeight W Q v w)
      = fun w => W.W u w - W.W u w * W.W v w := by
    funext w; unfold adjWeight; rw [if_pos hP, if_neg hQ]; ring
  rw [e, integral_sub (integrable_W_left W u) (integrable_W_mul W u v)]
  rfl

/-- Second-only pattern: `∫ (1-W(u,·))·W(v,·) = deg v - codeg u v`. -/
private lemma integral_adjWeight_FT {P Q : Prop} (hP : ¬ P) (hQ : Q) (W : Graphon) (u v : I) :
    ∫ w : I, adjWeight W P u w * adjWeight W Q v w = W.deg v - W.codeg u v := by
  have e : (fun w => adjWeight W P u w * adjWeight W Q v w)
      = fun w => W.W v w - W.W u w * W.W v w := by
    funext w; unfold adjWeight; rw [if_neg hP, if_pos hQ]; ring
  rw [e, integral_sub (integrable_W_left W v) (integrable_W_mul W u v)]
  show W.deg v - W.codeg u v = W.deg v - W.codeg u v
  rfl

/-- Neither-adjacent pattern: `∫ (1-W(u,·))·(1-W(v,·)) = 1 - deg u - deg v + codeg u v`. -/
private lemma integral_adjWeight_FF {P Q : Prop} (hP : ¬ P) (hQ : ¬ Q) (W : Graphon) (u v : I) :
    ∫ w : I, adjWeight W P u w * adjWeight W Q v w
      = 1 - W.deg u - W.deg v + W.codeg u v := by
  have e : (fun w => adjWeight W P u w * adjWeight W Q v w)
      = fun w => (1 - W.W u w - W.W v w) + W.W u w * W.W v w := by
    funext w; unfold adjWeight; rw [if_neg hP, if_neg hQ]; ring
  rw [e]
  have hInt3 : Integrable (fun w => (1:ℝ) - W.W u w - W.W v w) :=
    integrable_of_bounds'' (a := -1) (b := 1)
      ((measurable_const.sub (W.measurable_left u)).sub (W.measurable_left v))
      (fun w => by nlinarith [W.nonneg u w, W.le_one u w, W.nonneg v w, W.le_one v w])
      (fun w => by nlinarith [W.nonneg u w, W.nonneg v w])
  rw [integral_add hInt3 (integrable_W_mul W u v)]
  have hIntSum : Integrable (fun w => W.W u w + W.W v w) :=
    integrable_of_bounds'' (a := 0) (b := 2) ((W.measurable_left u).add (W.measurable_left v))
      (fun w => by linarith [W.nonneg u w, W.nonneg v w])
      (fun w => by linarith [W.le_one u w, W.le_one v w])
  have e2 : ∫ w : I, (1:ℝ) - W.W u w - W.W v w = 1 - W.deg u - W.deg v := by
    rw [show (fun w => (1:ℝ) - W.W u w - W.W v w)
        = fun w => (1:ℝ) - (W.W u w + W.W v w) from by funext w; ring,
      integral_sub (integrable_const 1) hIntSum,
      integral_add (integrable_W_left W u) (integrable_W_left W v)]
    simp only [integral_const, smul_eq_mul, MeasureTheory.probReal_univ, one_mul]
    unfold Graphon.deg
    ring
  rw [e2]
  show 1 - W.deg u - W.deg v + W.codeg u v = 1 - W.deg u - W.deg v + W.codeg u v
  rfl

private lemma rootCompatible_of_adj01 {σ' : FlagType (Fin 2)} {G : SimpleGraph (Fin 3)}
    (hRC : G.Adj 0 1 ↔ σ'.Adj 0 1) (hn : (2:ℕ) ≤ 3) : RootCompatible σ' hn G := by
  intro a b
  fin_cases a <;> fin_cases b
  · simp
  · exact hRC.symm
  · rw [σ'.adj_comm, G.adj_comm]; exact hRC.symm
  · simp

/-- **The shared reduction engine**: reduces `(graphonRootedHom W σ' u v h) (FlagAlgebra of a
generated 3-vertex flag F)` to `unnormRootedDensity W hn G u v / rootWeight W σ' u v`, given
`G` the (unique, by `stdRooted_filter_singleton`) standard-rooted witness. -/
private lemma dictionary_engine {σ' : FlagType (Fin 2)} (W : Graphon) (u v : I)
    (h : RootAdmissible W σ' u v) (F0 : FlagAlgebra σ') (Fr : Flag σ' (Fin 3))
    (hF0 : F0 = ⟦basisVector (⟨3, Fr⟩ : FinFlag σ')⟧)
    (G : SimpleGraph (Fin 3)) (hn : (2:ℕ) ≤ 3) (hRC : RootCompatible σ' hn G)
    (hGF : (⟦mkStdRooted σ' hn G hRC⟧ : Flag σ' (Fin 3)) = Fr) :
    (graphonRootedHom W σ' u v h) F0
      = unnormRootedDensity W hn G u v / rootWeight W σ' u v := by
  have hval : (graphonRootedHom W σ' u v h) F0
      = graphonRootedProfileFun W σ' u v ⟨3, Fr⟩ := by
    rw [hF0, ← PositiveHom.coe_flag, graphonRootedHom_coe]
  rw [hval]
  show graphonRootedProfileFun W σ' u v (⟨3, Fr⟩ : FinFlag σ') = _
  unfold graphonRootedProfileFun
  generalize hn3_eq : finFlag_size_ge_n₀ (⟨3, Fr⟩ : FinFlag σ') = hn3
  have hnn3 : hn = hn3 := hn3_eq
  subst hnn3
  rw [stdRooted_filter_singleton (σ' := σ') hn hRC hGF, Finset.sum_singleton]

/-! ## `a_τ` -/

private def G_atau : SimpleGraph (Fin 3) := mkG3 true true false

private lemma G_atau_adj01 : G_atau.Adj 0 1 := by unfold G_atau mkG3; tauto
private lemma G_atau_adj02 : G_atau.Adj 0 2 := by unfold G_atau mkG3; tauto
private lemma G_atau_not_adj12 : ¬ G_atau.Adj 1 2 := by
  unfold G_atau mkG3
  simp only
  decide

private lemma H_atau_adj01 : Sym2LabeledGraph_3_2_1_1.toLabeledGraph.graph.Adj 0 1 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_atau_adj02 : Sym2LabeledGraph_3_2_1_1.toLabeledGraph.graph.Adj 0 2 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_atau_not_adj12 : ¬ Sym2LabeledGraph_3_2_1_1.toLabeledGraph.graph.Adj 1 2 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_atau_type0 : Sym2LabeledGraph_3_2_1_1.toLabeledGraph.type_embed 0 = 0 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_type_embed_eq]; decide
private lemma H_atau_type1 : Sym2LabeledGraph_3_2_1_1.toLabeledGraph.type_embed 1 = 1 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_type_embed_eq]; decide

/-- `a_τ`: the rooted density of the third vertex adjacent to the first root only. -/
theorem graphonRootedHom_a_tau (W : Graphon) (u v : I)
    (h : RootAdmissible W FlagType_2_1 u v) :
    (graphonRootedHom W FlagType_2_1 u v h) FlagAlgebra_3_2_1_1
      = W.deg u - W.codeg u v := by
  have hn3 : (2:ℕ) ≤ 3 := by norm_num
  have hRCatau : RootCompatible FlagType_2_1 hn3 G_atau :=
    rootCompatible_of_adj01 ⟨fun _ => tau_adj01, fun _ => G_atau_adj01⟩ hn3
  have hGF : (⟦mkStdRooted FlagType_2_1 hn3 G_atau hRCatau⟧ : Flag FlagType_2_1 (Fin 3))
      = Flag_3_2_1_1 :=
    mkStdRooted_eq_of_iso hn3 hRCatau Sym2LabeledGraph_3_2_1_1.toLabeledGraph (Equiv.refl (Fin 3))
      (graph3_iso_ext (Equiv.refl (Fin 3))
        ⟨fun _ => G_atau_adj01, fun _ => H_atau_adj01⟩
        ⟨fun _ => G_atau_adj02, fun _ => H_atau_adj02⟩
        ⟨fun hh => absurd hh H_atau_not_adj12, fun hh => absurd hh G_atau_not_adj12⟩)
      (by simpa using H_atau_type0.symm) (by simpa using H_atau_type1.symm)
  rw [dictionary_engine W u v h FlagAlgebra_3_2_1_1 Flag_3_2_1_1 rfl G_atau hn3 hRCatau hGF,
    unnormRootedDensity_pattern G_atau hn3 W u v,
    integral_adjWeight_TF G_atau_adj02 G_atau_not_adj12 W u v]
  have hrootW : rootWeight W FlagType_2_1 u v = W.W u v := by
    show adjWeight W (FlagType_2_1.Adj 0 1) u v = W.W u v
    unfold adjWeight; rw [if_pos tau_adj01]
  have hrw : adjWeight W (G_atau.Adj 0 1) u v = W.W u v := by
    unfold adjWeight; rw [if_pos G_atau_adj01]
  have hpos : (0:ℝ) < W.W u v := hrootW ▸ h
  rw [hrw, hrootW]
  field_simp

/-! ## `b_τ` -/

private def G_btau : SimpleGraph (Fin 3) := mkG3 true false true

private lemma G_btau_adj01 : G_btau.Adj 0 1 := by unfold G_btau mkG3; tauto
private lemma G_btau_not_adj02 : ¬ G_btau.Adj 0 2 := by
  unfold G_btau mkG3; simp only; decide
private lemma G_btau_adj12 : G_btau.Adj 1 2 := by unfold G_btau mkG3; tauto

private lemma H_btau_adj01 : Sym2LabeledGraph_3_2_1_2.toLabeledGraph.graph.Adj 0 1 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_btau_adj02 : Sym2LabeledGraph_3_2_1_2.toLabeledGraph.graph.Adj 0 2 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_btau_not_adj12 : ¬ Sym2LabeledGraph_3_2_1_2.toLabeledGraph.graph.Adj 1 2 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_btau_type0 : Sym2LabeledGraph_3_2_1_2.toLabeledGraph.type_embed 0 = 1 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_type_embed_eq]; decide
private lemma H_btau_type1 : Sym2LabeledGraph_3_2_1_2.toLabeledGraph.type_embed 1 = 0 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_type_embed_eq]; decide

/-- `b_τ`: the rooted density of the third vertex adjacent to the second root only. -/
theorem graphonRootedHom_b_tau (W : Graphon) (u v : I)
    (h : RootAdmissible W FlagType_2_1 u v) :
    (graphonRootedHom W FlagType_2_1 u v h) FlagAlgebra_3_2_1_2
      = W.deg v - W.codeg u v := by
  have hn3 : (2:ℕ) ≤ 3 := by norm_num
  have hRCbtau : RootCompatible FlagType_2_1 hn3 G_btau :=
    rootCompatible_of_adj01 ⟨fun _ => tau_adj01, fun _ => G_btau_adj01⟩ hn3
  have hGF : (⟦mkStdRooted FlagType_2_1 hn3 G_btau hRCbtau⟧ : Flag FlagType_2_1 (Fin 3))
      = Flag_3_2_1_2 :=
    mkStdRooted_eq_of_iso hn3 hRCbtau Sym2LabeledGraph_3_2_1_2.toLabeledGraph (Equiv.swap 0 1)
      (graph3_iso_ext (Equiv.swap 0 1)
        (by simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
            rw [Sym2LabeledGraph_3_2_1_2.toLabeledGraph.graph.adj_comm]
            exact ⟨fun _ => G_btau_adj01, fun _ => H_btau_adj01⟩)
        (by simp only [Equiv.swap_apply_left,
              show Equiv.swap (0:Fin 3) 1 2 = 2 from
                Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
            exact ⟨fun hh => absurd hh H_btau_not_adj12, fun hh => absurd hh G_btau_not_adj02⟩)
        (by simp only [Equiv.swap_apply_right,
              show Equiv.swap (0:Fin 3) 1 2 = 2 from
                Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
            exact ⟨fun _ => G_btau_adj12, fun _ => H_btau_adj02⟩))
      (by simpa using H_btau_type0.symm) (by simpa using H_btau_type1.symm)
  rw [dictionary_engine W u v h FlagAlgebra_3_2_1_2 Flag_3_2_1_2 rfl G_btau hn3 hRCbtau hGF,
    unnormRootedDensity_pattern G_btau hn3 W u v,
    integral_adjWeight_FT G_btau_not_adj02 G_btau_adj12 W u v]
  have hrootW : rootWeight W FlagType_2_1 u v = W.W u v := by
    show adjWeight W (FlagType_2_1.Adj 0 1) u v = W.W u v
    unfold adjWeight; rw [if_pos tau_adj01]
  have hrw : adjWeight W (G_btau.Adj 0 1) u v = W.W u v := by
    unfold adjWeight; rw [if_pos G_btau_adj01]
  have hpos : (0:ℝ) < W.W u v := hrootW ▸ h
  rw [hrw, hrootW]
  field_simp

/-! ## `g_τ` -/

private def G_gtau : SimpleGraph (Fin 3) := mkG3 true true true

private lemma G_gtau_adj01 : G_gtau.Adj 0 1 := by unfold G_gtau mkG3; tauto
private lemma G_gtau_adj02 : G_gtau.Adj 0 2 := by unfold G_gtau mkG3; tauto
private lemma G_gtau_adj12 : G_gtau.Adj 1 2 := by unfold G_gtau mkG3; tauto

private lemma H_gtau_adj01 : Sym2LabeledGraph_3_2_1_3.toLabeledGraph.graph.Adj 0 1 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_gtau_adj02 : Sym2LabeledGraph_3_2_1_3.toLabeledGraph.graph.Adj 0 2 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_gtau_adj12 : Sym2LabeledGraph_3_2_1_3.toLabeledGraph.graph.Adj 1 2 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_gtau_type0 : Sym2LabeledGraph_3_2_1_3.toLabeledGraph.type_embed 0 = 0 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_type_embed_eq]; decide
private lemma H_gtau_type1 : Sym2LabeledGraph_3_2_1_3.toLabeledGraph.type_embed 1 = 1 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_type_embed_eq]; decide

/-- `g_τ`: the rooted density of the third vertex adjacent to both roots. -/
theorem graphonRootedHom_g_tau (W : Graphon) (u v : I)
    (h : RootAdmissible W FlagType_2_1 u v) :
    (graphonRootedHom W FlagType_2_1 u v h) FlagAlgebra_3_2_1_3
      = W.codeg u v := by
  have hn3 : (2:ℕ) ≤ 3 := by norm_num
  have hRCgtau : RootCompatible FlagType_2_1 hn3 G_gtau :=
    rootCompatible_of_adj01 ⟨fun _ => tau_adj01, fun _ => G_gtau_adj01⟩ hn3
  have hGF : (⟦mkStdRooted FlagType_2_1 hn3 G_gtau hRCgtau⟧ : Flag FlagType_2_1 (Fin 3))
      = Flag_3_2_1_3 :=
    mkStdRooted_eq_of_iso hn3 hRCgtau Sym2LabeledGraph_3_2_1_3.toLabeledGraph (Equiv.refl (Fin 3))
      (graph3_iso_ext (Equiv.refl (Fin 3))
        ⟨fun _ => G_gtau_adj01, fun _ => H_gtau_adj01⟩
        ⟨fun _ => G_gtau_adj02, fun _ => H_gtau_adj02⟩
        ⟨fun _ => G_gtau_adj12, fun _ => H_gtau_adj12⟩)
      (by simpa using H_gtau_type0.symm) (by simpa using H_gtau_type1.symm)
  rw [dictionary_engine W u v h FlagAlgebra_3_2_1_3 Flag_3_2_1_3 rfl G_gtau hn3 hRCgtau hGF,
    unnormRootedDensity_pattern G_gtau hn3 W u v,
    integral_adjWeight_TT G_gtau_adj02 G_gtau_adj12 W u v]
  have hrootW : rootWeight W FlagType_2_1 u v = W.W u v := by
    show adjWeight W (FlagType_2_1.Adj 0 1) u v = W.W u v
    unfold adjWeight; rw [if_pos tau_adj01]
  have hrw : adjWeight W (G_gtau.Adj 0 1) u v = W.W u v := by
    unfold adjWeight; rw [if_pos G_gtau_adj01]
  have hpos : (0:ℝ) < W.W u v := hrootW ▸ h
  rw [hrw, hrootW]
  field_simp

/-! ## `z_η` -/

private def G_zeta : SimpleGraph (Fin 3) := mkG3 false false false

private lemma G_zeta_not_adj01 : ¬ G_zeta.Adj 0 1 := by unfold G_zeta mkG3; simp only; decide
private lemma G_zeta_not_adj02 : ¬ G_zeta.Adj 0 2 := by unfold G_zeta mkG3; simp only; decide
private lemma G_zeta_not_adj12 : ¬ G_zeta.Adj 1 2 := by unfold G_zeta mkG3; simp only; decide

private lemma H_zeta_not_adj01 : ¬ Sym2LabeledGraph_3_2_0_0.toLabeledGraph.graph.Adj 0 1 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_zeta_not_adj02 : ¬ Sym2LabeledGraph_3_2_0_0.toLabeledGraph.graph.Adj 0 2 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_zeta_not_adj12 : ¬ Sym2LabeledGraph_3_2_0_0.toLabeledGraph.graph.Adj 1 2 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_zeta_type0 : Sym2LabeledGraph_3_2_0_0.toLabeledGraph.type_embed 0 = 0 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_type_embed_eq]; decide
private lemma H_zeta_type1 : Sym2LabeledGraph_3_2_0_0.toLabeledGraph.type_embed 1 = 1 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_type_embed_eq]; decide

/-- `z_η`: the rooted density of the third vertex adjacent to neither root (non-edge type). -/
theorem graphonRootedHom_z_eta (W : Graphon) (u v : I)
    (h : RootAdmissible W FlagType_2_0 u v) :
    (graphonRootedHom W FlagType_2_0 u v h) FlagAlgebra_3_2_0_0
      = 1 - W.deg u - W.deg v + W.codeg u v := by
  have hn3 : (2:ℕ) ≤ 3 := by norm_num
  have hRCzeta : RootCompatible FlagType_2_0 hn3 G_zeta :=
    rootCompatible_of_adj01
      ⟨fun hh => absurd hh G_zeta_not_adj01, fun hh => absurd hh eta_not_adj01⟩ hn3
  have hGF : (⟦mkStdRooted FlagType_2_0 hn3 G_zeta hRCzeta⟧ : Flag FlagType_2_0 (Fin 3))
      = Flag_3_2_0_0 :=
    mkStdRooted_eq_of_iso hn3 hRCzeta Sym2LabeledGraph_3_2_0_0.toLabeledGraph (Equiv.refl (Fin 3))
      (graph3_iso_ext (Equiv.refl (Fin 3))
        ⟨fun hh => absurd hh H_zeta_not_adj01, fun hh => absurd hh G_zeta_not_adj01⟩
        ⟨fun hh => absurd hh H_zeta_not_adj02, fun hh => absurd hh G_zeta_not_adj02⟩
        ⟨fun hh => absurd hh H_zeta_not_adj12, fun hh => absurd hh G_zeta_not_adj12⟩)
      (by simpa using H_zeta_type0.symm) (by simpa using H_zeta_type1.symm)
  rw [dictionary_engine W u v h FlagAlgebra_3_2_0_0 Flag_3_2_0_0 rfl G_zeta hn3 hRCzeta hGF,
    unnormRootedDensity_pattern G_zeta hn3 W u v,
    integral_adjWeight_FF G_zeta_not_adj02 G_zeta_not_adj12 W u v]
  have hrootW : rootWeight W FlagType_2_0 u v = 1 - W.W u v := by
    show adjWeight W (FlagType_2_0.Adj 0 1) u v = 1 - W.W u v
    unfold adjWeight; rw [if_neg eta_not_adj01]
  have hrw : adjWeight W (G_zeta.Adj 0 1) u v = 1 - W.W u v := by
    unfold adjWeight; rw [if_neg G_zeta_not_adj01]
  have hpos : (0:ℝ) < 1 - W.W u v := hrootW ▸ h
  rw [hrw, hrootW]
  field_simp

/-! ## `g_η` -/

private def G_geta : SimpleGraph (Fin 3) := mkG3 false true true

private lemma G_geta_not_adj01 : ¬ G_geta.Adj 0 1 := by unfold G_geta mkG3; simp only; decide
private lemma G_geta_adj02 : G_geta.Adj 0 2 := by unfold G_geta mkG3; tauto
private lemma G_geta_adj12 : G_geta.Adj 1 2 := by unfold G_geta mkG3; tauto

private lemma H_geta_adj01 : Sym2LabeledGraph_3_2_0_3.toLabeledGraph.graph.Adj 0 1 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_geta_adj02 : Sym2LabeledGraph_3_2_0_3.toLabeledGraph.graph.Adj 0 2 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_geta_not_adj12 : ¬ Sym2LabeledGraph_3_2_0_3.toLabeledGraph.graph.Adj 1 2 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_adj_iff]; decide
private lemma H_geta_type0 : Sym2LabeledGraph_3_2_0_3.toLabeledGraph.type_embed 0 = 1 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_type_embed_eq]; decide
private lemma H_geta_type1 : Sym2LabeledGraph_3_2_0_3.toLabeledGraph.type_embed 1 = 2 := by
  rw [FlagAlgebras.Compute.Sym2LabeledGraph.toLabeledGraph_type_embed_eq]; decide

/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` of `Fin 3` (the root-transport permutation for `g_η`, whose
generator representative places the roots at positions `1, 2`). -/
private def cyc3 : Fin 3 ≃ Fin 3 where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide
  right_inv := by decide

private lemma cyc3_apply0 : cyc3 0 = 1 := rfl
private lemma cyc3_apply1 : cyc3 1 = 2 := rfl
private lemma cyc3_apply2 : cyc3 2 = 0 := rfl

/-- `g_η`: the rooted density of the third vertex adjacent to both roots (non-edge type). -/
theorem graphonRootedHom_g_eta (W : Graphon) (u v : I)
    (h : RootAdmissible W FlagType_2_0 u v) :
    (graphonRootedHom W FlagType_2_0 u v h) FlagAlgebra_3_2_0_3
      = W.codeg u v := by
  have hn3 : (2:ℕ) ≤ 3 := by norm_num
  have hRCgeta : RootCompatible FlagType_2_0 hn3 G_geta :=
    rootCompatible_of_adj01
      ⟨fun hh => absurd hh G_geta_not_adj01, fun hh => absurd hh eta_not_adj01⟩ hn3
  have hGF : (⟦mkStdRooted FlagType_2_0 hn3 G_geta hRCgeta⟧ : Flag FlagType_2_0 (Fin 3))
      = Flag_3_2_0_3 :=
    mkStdRooted_eq_of_iso hn3 hRCgeta Sym2LabeledGraph_3_2_0_3.toLabeledGraph cyc3
      (graph3_iso_ext cyc3
        (by rw [cyc3_apply0, cyc3_apply1]
            exact ⟨fun hh => absurd hh H_geta_not_adj12, fun hh => absurd hh G_geta_not_adj01⟩)
        (by rw [cyc3_apply0, cyc3_apply2,
              Sym2LabeledGraph_3_2_0_3.toLabeledGraph.graph.adj_comm]
            exact ⟨fun _ => G_geta_adj02, fun _ => H_geta_adj01⟩)
        (by rw [cyc3_apply1, cyc3_apply2,
              Sym2LabeledGraph_3_2_0_3.toLabeledGraph.graph.adj_comm]
            exact ⟨fun _ => G_geta_adj12, fun _ => H_geta_adj02⟩))
      (by simpa using H_geta_type0.symm) (by simpa using H_geta_type1.symm)
  rw [dictionary_engine W u v h FlagAlgebra_3_2_0_3 Flag_3_2_0_3 rfl G_geta hn3 hRCgeta hGF,
    unnormRootedDensity_pattern G_geta hn3 W u v,
    integral_adjWeight_TT G_geta_adj02 G_geta_adj12 W u v]
  have hrootW : rootWeight W FlagType_2_0 u v = 1 - W.W u v := by
    show adjWeight W (FlagType_2_0.Adj 0 1) u v = 1 - W.W u v
    unfold adjWeight; rw [if_neg eta_not_adj01]
  have hrw : adjWeight W (G_geta.Adj 0 1) u v = 1 - W.W u v := by
    unfold adjWeight; rw [if_neg G_geta_not_adj01]
  have hpos : (0:ℝ) < 1 - W.W u v := hrootW ▸ h
  rw [hrw, hrootW]
  field_simp

/-! ## The transport to almost-everywhere kernel equations -/

/-- **The `τ`-transport**: for a graphon in the `K₄`-free `P₄`-slice, `R_τ(3) = 0`.

Proof route: `k4freeP4_tau_equation` + `k4freeP4_tau_symm` hold for every
`χ ∈ relSσ k4freeP4Slice FlagType_2_1`; by `support_subset_relSσ` (at `φ₀ := graphonHom W`,
membership `hmem`, admissibility `hσ`) and `Measure.support_mem_ae` they hold
`ℙ[φ_W]`-a.e.; by `rootedViewMeasure_eq_extend` and `MeasureTheory.ae_map_iff` (the
evaluation predicates are measurable: coordinate evaluations on the profile space) they hold
at `rootedViewPoint W _ z` for `withDensity`-a.e. `z`, i.e. for volume-a.e. `z` with
`rootWeight ≠ 0`; on the admissible set rewrite through the dictionary
(`graphonRootedHom_a_tau/_b_tau/_g_tau`) to get
`W z ≠ 0 → (3−2)·((d(u)−c) + (d(v)−c)) = 2·c` a.e. — the statement `ellTau 3 = 0` — and
conclude with `Rtau_eq_zero_iff_ae`. -/
theorem k4freeP4_graphon_Rtau_eq_zero (W : Graphon)
    (hσ : (graphonHom W) ⟨FlagType_2_1⟩₀ > 0)
    (hmem : posHomPoint (graphonHom W) ∈ k4freeP4Slice) :
    W.Rtau 3 = 0 := by
  rw [W.Rtau_eq_zero_iff_ae]
  -- The mined `τ`-equation holds `ℙ[φ_W]`-a.e. (the equation alone already forces
  -- `ellTau 3 = 0`; the symmetry `k4freeP4_tau_symm` is not needed for this conclusion).
  have hae1 : ∀ᵐ χ ∂ (ℙ[graphonHom W] : Measure (PositiveHomSpace FlagType_2_1)),
      (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_1
        + (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_2
        = 2 * (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_1_3 := by
    filter_upwards [Measure.support_mem_ae] with χ hχ
    exact k4freeP4_tau_equation χ (support_subset_relSσ hmem hσ hχ)
  -- Transport through the rooted-view measure to `rootWeight`-a.e. pairs `(u, v)`.
  rw [← rootedViewMeasure_eq_extend W FlagType_2_1 hσ] at hae1
  unfold rootedViewMeasure at hae1
  have hcne : (ENNReal.ofReal (rootMass W FlagType_2_1))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  rw [Measure.ae_ennreal_smul_measure_iff hcne] at hae1
  have hae2 := ae_of_ae_map (measurable_rootedViewPoint W FlagType_2_1).aemeasurable hae1
  have hmeasf : Measurable (fun z : I × I => ENNReal.ofReal (rootWeight W FlagType_2_1 z.1 z.2)) :=
    (measurable_rootWeight W FlagType_2_1).ennreal_ofReal
  have hae3 := (ae_withDensity_iff hmeasf).mp hae2
  filter_upwards [hae3] with z hz
  by_cases hadm : RootAdmissible W FlagType_2_1 z.1 z.2
  · right
    have hne : ENNReal.ofReal (rootWeight W FlagType_2_1 z.1 z.2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hadm).ne'
    have heq := hz hne
    rw [rootedViewPoint_of_admissible W FlagType_2_1 z hadm, toPosHom_posHomPoint] at heq
    rw [graphonRootedHom_a_tau, graphonRootedHom_b_tau, graphonRootedHom_g_tau] at heq
    unfold Graphon.ellTau
    push_cast
    linarith [heq]
  · left
    unfold RootAdmissible at hadm
    unfold rootWeight adjWeight at hadm
    rw [if_pos tau_adj01] at hadm
    linarith [not_lt.mp hadm, W.nonneg z.1 z.2]

/-- **The `η`-transport**: for a graphon in the `K₄`-free `P₄`-slice, `R_η(3) = 0`.
(Same scheme as `k4freeP4_graphon_Rtau_eq_zero`, through `k4freeP4_eta_equation` and the
`z_η`/`g_η` dictionary; the non-edge weight `1 − W` plays the role of `rootWeight`.) -/
theorem k4freeP4_graphon_Reta_eq_zero (W : Graphon)
    (hσ : (graphonHom W) ⟨FlagType_2_0⟩₀ > 0)
    (hmem : posHomPoint (graphonHom W) ∈ k4freeP4Slice) :
    W.Reta 3 = 0 := by
  rw [W.Reta_eq_zero_iff_ae]
  have hae1 : ∀ᵐ χ ∂ (ℙ[graphonHom W] : Measure (PositiveHomSpace FlagType_2_0)),
      2 * (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_0
        = (PositiveHomSpace.toPosHom χ) FlagAlgebra_3_2_0_3 := by
    filter_upwards [Measure.support_mem_ae] with χ hχ
    exact k4freeP4_eta_equation χ (support_subset_relSσ hmem hσ hχ)
  rw [← rootedViewMeasure_eq_extend W FlagType_2_0 hσ] at hae1
  unfold rootedViewMeasure at hae1
  have hcne : (ENNReal.ofReal (rootMass W FlagType_2_0))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  rw [Measure.ae_ennreal_smul_measure_iff hcne] at hae1
  have hae2 := ae_of_ae_map (measurable_rootedViewPoint W FlagType_2_0).aemeasurable hae1
  have hmeasf : Measurable (fun z : I × I => ENNReal.ofReal (rootWeight W FlagType_2_0 z.1 z.2)) :=
    (measurable_rootWeight W FlagType_2_0).ennreal_ofReal
  have hae3 := (ae_withDensity_iff hmeasf).mp hae2
  filter_upwards [hae3] with z hz
  by_cases hadm : RootAdmissible W FlagType_2_0 z.1 z.2
  · right
    have hne : ENNReal.ofReal (rootWeight W FlagType_2_0 z.1 z.2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hadm).ne'
    have heq := hz hne
    rw [rootedViewPoint_of_admissible W FlagType_2_0 z hadm, toPosHom_posHomPoint] at heq
    rw [graphonRootedHom_z_eta, graphonRootedHom_g_eta] at heq
    unfold Graphon.ellEta
    push_cast
    linarith [heq]
  · left
    unfold RootAdmissible at hadm
    unfold rootWeight adjWeight at hadm
    rw [if_neg eta_not_adj01] at hadm
    have h1 := W.le_one z.1 z.2
    linarith [not_lt.mp hadm]

/-- **The assembled tripartite conclusion**: any graphon whose `φ_W` lies in the `K₄`-free
`P₄`-slice (with both root types of positive mass) is almost everywhere the balanced
complete tripartite graphon — `Graphon.r3_rigidity` with both hypotheses discharged by the
rooted transport.  This is the graphon-side content of `thm:k4free-p4-tripartite` (Thm 102);
composing with the representation theorem yields the paper statement verbatim. -/
theorem k4freeP4_graphon_tripartite (W : Graphon)
    (hστ : (graphonHom W) ⟨FlagType_2_1⟩₀ > 0)
    (hση : (graphonHom W) ⟨FlagType_2_0⟩₀ > 0)
    (hmem : posHomPoint (graphonHom W) ∈ k4freeP4Slice) :
    ∃ P : I → Fin 3, Measurable P
      ∧ (∀ i, volume (P ⁻¹' {i}) = ENNReal.ofReal (1 / 3))
      ∧ ∀ᵐ z : I × I, W.W z.1 z.2 = if P z.1 = P z.2 then 0 else 1 :=
  W.r3_rigidity (k4freeP4_graphon_Rtau_eq_zero W hστ hmem)
    (k4freeP4_graphon_Reta_eq_zero W hση hmem)

end FlagAlgebras.MetaTheory
