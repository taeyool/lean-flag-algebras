# Architecture of the MetaTheory formalisation

This document describes how the 23 Lean modules fit together: the proof strategy, the dependency
layers, a module-by-module map, and a walkthrough of the capstone proof. See
[`README.md`](./README.md) for the results and verification status, and
[`READING_GUIDE.md`](./READING_GUIDE.md) for conventions and a reading order.

All modules live in namespace `FlagAlgebras.MetaTheory` and are aggregated by
[`../MetaTheory.lean`](../MetaTheory.lean).

---

## The proof strategy in one paragraph

Fix a forbidden family (a *constrained class*) and a type `σ`. Two semantics for "`f ≥ 0`" exist:
the **quotient** semantics (`f ≥ 0` on `Q_σ`, the homomorphisms vanishing on forbidden flags) and
the **ensemble** semantics (`f ≥ 0` almost surely under every admissible random extension). The
**support-closure criterion** (§4) reduces their equivalence — for *every* `f` — to a topological
identity `S_σ = Q_σ`, where `S_σ` is the closure of the supports of the admissible random
extensions. Soundness (`S_σ ⊆ Q_σ`) is §3's "support passes" lemma. The hard direction,
`Q_σ ⊆ S_σ` (**root-plantability**), is §5's main theorem: for a **clone-closed** class one takes
a target `ψ ∈ Q_σ`, represents it by *in-class* finite flags, **blows them up** so the type can be
*planted*, and shows — via weak convergence + Portmanteau — that the planted blow-ups put positive
mass arbitrarily close to `ψ`, so `ψ ∈ S_σ`.

---

## Dependency layers

Arrows point from a module to the modules it imports (within `MetaTheory`; every module also sits
on the surrounding `LeanFlagAlgebras/FlagAlgebra/` base). Read bottom-up.

```
  §2–§4 foundations          §5 blow-up + counting              §5 capstone machinery
  ─────────────────          ─────────────────────              ─────────────────────
  MeasureSupport             Blowup                             ConstrainedRep ───────────┐
     │                          │   │                            (constrained rep. thm)   │
  EvalAlgebra                BlowupFlag│                                                   │
     │      │                   │   │ │                          RootingUniform ──────────┤
  ConstrainedClass             │   │ DensityBridge                (measure = label ratio)  │
     │      │                   │   │   │                                                  │
  SupportClosure  MeasureUniq.  │   │ LabeledCount                MeasureUniqueness        │
     │  │  (used by WeakConv)   │   │   │  │                          │                    │
  ForbiddenIdeal               CloneCount│ │                       WeakConvergence ────────┤
                                  │   │   │ │                       (rooting ⇒ ℙ[φ₀])       │
                               CloneTotal │ │                                              │
                                  │   PlantedCount                  GraphClassConstraint   │
                                  │       │                          ↑ InducedContainment  │
                                  └─► PlantedEstimate ◄──────────────┘                     │
                                          │   ▲                       BlowupSequence ───────┤
                                  BinomialRatio                        (base limit φ₀)      │
                                  (ρ → 1 limits)                                            │
                                                                                           ▼
  ProductTV  (superseded;                                            ┌──────────────────────┐
  not on the critical path)                                          │     CloneClosed      │
                                                                     │  clone_root_plantable│
                                                                     │  cor:clique-free     │
                                                                     └──────────────────────┘
```

The capstone [`CloneClosed`](./CloneClosed.lean) imports, directly or transitively, **every other
module except two**: `ProductTV` (superseded — see Deviation 1 in the README) and `ForbiddenIdeal`
(the standalone §3 faithfulness result, not used as a lemma downstream). Both are reached only by
the aggregator.

---

## Module-by-module map

### §2–§4 foundations

* **[`MeasureSupport`](./MeasureSupport.lean)** — §2 `lem:support-as`.
  `ae_nonneg_iff_nonneg_on_support`: for a probability measure on a hereditarily-Lindelöf space and
  continuous `h`, `μ{0 ≤ h} = 1 ⇔ 0 ≤ h` on `supp μ`. Forward: a support point meets every
  positive-measure nbhd; backward: the support is conull. Mathlib-only.

* **[`EvalAlgebra`](./EvalAlgebra.lean)** — the Stone–Weierstrass layer (supports §4 and §5).
  `evalAlgHom : A^σ →ₐ[ℝ] C(X_σ, ℝ)` (flag evaluation), `continuous_eval`, `evalSubalgebra`,
  `evalSubalgebra_dense` (separates points ⟹ sup-norm dense), and `exists_flag_near` (ε-approx of
  any continuous function by a flag evaluation).

* **[`ConstrainedClass`](./ConstrainedClass.lean)** — §3 quotient algebra. `forbiddenIdeal`,
  `ConstrainedAlgebra = A^σ ⧸ forbiddenIdeal`, the quotient map `qmap`, the supported space `Qσ`,
  the intrinsic characterisation `mem_Qσ_iff` (`χ ∈ Q_σ ⇔ χ` vanishes on every forbidden flag,
  backward direction via the ring-quotient universal property), and `Qσ_isClosed`.

* **[`SupportClosure`](./SupportClosure.lean)** — §3 `lem:support-passes-general` + all of §4.
  The `Constraint σ` structure (forbidden σ-flags `forbσ`, forbidden graphs `forb0`, the
  unlabelling link), `support_passes` (`supp ℙ[φ₀] ⊆ Q_σ`), `Sσ`/`RootPlantable` (`def:root-planting`),
  `Sσ_subset_Qσ`, and `support_criterion` (`thm:support-criterion`). The hard direction of the
  criterion separates `ψ ∈ Q_σ \ S_σ` by **Urysohn in the compact metric `X_σ`** then approximates
  the separating function by a flag via `exists_flag_near`.

* **[`ForbiddenIdeal`](./ForbiddenIdeal.lean)** — §3 faithfulness. `forbiddenIdeal_eq_span`: under
  heredity (taken as a hypothesis), the forbidden ideal and the ℝ-span of the forbidden flags have
  equal carriers. Builds the span's ideal structure and does a two-way carrier inclusion.

* **[`MeasureUniqueness`](./MeasureUniqueness.lean)** — measure-theoretic dual of `EvalAlgebra`
  (input to weak convergence). `measure_eq_of_integral_flag_eq`: a probability measure on `X_σ` is
  determined by its flag-integrals (the integration functionals agree on the dense evaluation
  subalgebra, hence everywhere).

### §5 blow-up construction and the planted-estimate counting

* **[`Blowup`](./Blowup.lean)** — §5 `def:independent-blow-up` + `lem:planted-mass`.
  `independentBlowup G m` (host `Σ v, Fin (m v)`, adjacency from the base), `blowupProj`,
  `cliqueFree_independentBlowup` (the core of `cor:clique-free`), `blowupEmbeddings`/`plantedEmbeddings`
  with cardinalities, and `planted_mass` (`#planted/#all ≥ (λ/2k)^k`).

* **[`BlowupFlag`](./BlowupFlag.lean)** — `baseLabeledGraph`/`blowupLabeledGraph` (base / planted-
  blow-up as σ-flags) and `blowupGoodIso` (on a transversal the induced labelled subgraph of the
  blow-up is `≃f`, via projection, that of the base), giving `good_event_induces_iff`.

* **[`DensityBridge`](./DensityBridge.lean)** — `flagDensity₁_eq_count_div`: the density `p(F,G)`
  as `labeledGraphCount F G / binom`, stated for **any finite host** (needed for the `Σ`-host
  blow-up).

* **[`LabeledCount`](./LabeledCount.lean)** — `labeledGraphCount_eq_subset_count` and
  `flagDensity₁_eq_subset_count_div`: flag density as a **vertex-subset-sampling probability**.

* **[`CloneCount`](./CloneCount.lean)** — `clone_fiber_card`: blow-up subsets projecting
  injectively onto a base set `W` number `∏_{v∈W} m v` (the clone multiplicity).

* **[`CloneTotal`](./CloneTotal.lean)** — `clone_total_card` and `clone_total_card_const`: the
  total good size-`r` superset count, `C(|S₀|,r)·M^r` for equal clones (the form used downstream).

* **[`PlantedCount`](./PlantedCount.lean)** — `good_event_count`: the good blow-up subsets inducing
  `F₀` counted fiberwise as `∑_W ∏_{v∈W∖roots} m v` over base subsets `W` inducing `F₀` (each good
  subset = forced planted roots + a free clone choice over `W∖roots`).

* **[`PlantedEstimate`](./PlantedEstimate.lean)** — §5 `lem:planted-estimate` (uniform non-root
  clones). `planted_estimate`: `|p(F₀,blowup) − p(F₀,base)| ≤ 1 − ρ`. The good/bad split
  `A_good ≤ A_blow ≤ A_good + (T_all − T_good)` is closed by a rational sandwich (`nlinarith`).
  The largest, most intricate of the supporting modules.

* **[`ProductTV`](./ProductTV.lean)** — *(superseded / unused — see README Deviation 1).* The
  product-distribution total-variation bound `prod_tv_bound` and `l1_normalization_bound`
  (`eq:good-unnormalized-weight-bound`), correct but not on the uniform-clone critical path.

### §5 capstone machinery

* **[`BinomialRatio`](./BinomialRatio.lean)** — the analytic core of the uniform-clone estimate.
  `rho_tendsto_atTop`: `ρ(n,M) → descFactorial(n−k,r)/n^r` as `M→∞`; `rho_inf_tendsto_one`: that
  limit `→ 1` as `n→∞`. Together they drive `1 − ρ → 0`.

* **[`InducedContainment`](./InducedContainment.lean)** — the density/containment bridge.
  `exists_graph_embedding_of_flagDensity₁_ne_zero`: positive density of an unlabelled `D` in `H`
  yields a graph embedding `D.graph ↪g H.graph` — exactly what `CliqueFree.comap` consumes.

* **[`GraphClassConstraint`](./GraphClassConstraint.lean)** — the hereditary clone-closed package.
  The `GraphClass` structure (`Mem` + `comap` heredity + `clone_closed`), the derived `Constraint`
  (`constraintOf`), the two consumption lemmas `mem_of_forbiddenFree` (forbidden-free ⟹ in class,
  via `flagDensity_self = 1`) and `forbiddenFree_of_mem` (in class ⟹ forbidden-free, via the
  containment bridge + `comap`), and the instance `cliqueFreeClass r`.

* **[`ConstrainedRep`](./ConstrainedRep.lean)** — the **constrained representation theorem**
  `exists_constrained_flagSeq_limit` (the foundational new input; see README Deviation 2). A
  positive hom vanishing on all forbidden flags is the limit of *forbidden-free* flags.

* **[`RootingUniform`](./RootingUniform.lean)** — the σ-rooting measure as a uniform count.
  `toProbMeasure_apply_eq_dnf_ratio` (measure = `downwardNormalizingFactor`-ratio over labelings
  with profile in the set) and `sum_isomorphismCount_labelExtensions` (`∑ isomorphismCount = #σ-rootings`),
  together giving "measure(A) = #{rootings with profile ∈ A}/#{rootings}". This is what turns
  `planted_mass` (an embedding ratio) into a measure lower bound.

* **[`WeakConvergence`](./WeakConvergence.lean)** — `tendsto_rootingMeasure_extend`: the rooting
  measures of *any* converging flag sequence converge weakly (on `FlagDensitySpace σ`) to
  `(ℙ[φ₀]).map Subtype.val` (see README Deviation 3). Proof: every subsequential limit equals the
  target (Prokhorov + the integral identification + `measure_eq_of_integral_flag_eq` uniqueness).

* **[`BlowupSequence`](./BlowupSequence.lean)** — the base side of the capstone. The uniform
  `(M+1)`-blow-up flag sequence `blowupFlagSeq` (presented on `Fin (n·(M+1))`), its subsequential
  limit `exists_blowup_limit`, and the two key properties `blowup_limit_mem_Q0`
  (`posHomPoint φ₀ ∈ Q0`) and `blowup_limit_type_pos` (`φ₀⟨σ⟩₀ ≥ 1/n^{n₀} > 0`).

### The capstone

* **[`CloneClosed`](./CloneClosed.lean)** — `thm:clone-root-plantable` + `cor:clique-free`.
  `clone_root_plantable`, `clique_free_root_plantable`, `clique_free_quotient_iff_ensemble`. Wires
  everything above together (walkthrough below).

---

## The capstone proof, step by step (`clone_root_plantable`)

Goal: `RootPlantable (constraintOf gc σ)`, i.e. `S_σ = Q_σ`. The inclusion `S_σ ⊆ Q_σ` is
`Sσ_subset_Qσ`. For `Q_σ ⊆ S_σ`, take `ψ ∈ Q_σ` and show `ψ ∈ S_σ = closure(⋃ supp ℙ[φ₀])`.

1. **Reduce to finite cylinders.** `mem_closure_of_forall_finset_cylinder` reduces `ψ ∈ closure A`
   to: for every finite flag set `Fs` and `ε > 0`, some admissible `supp ℙ[φ₀]` meets the cylinder
   `{χ : ∀ Fi ∈ Fs, |χ.val Fi − ψ.val Fi| < ε}` (the product topology of `X_σ ⊆ FlagDensitySpace σ`).

2. **Choose the base flag `G_t`.** `mem_Qσ_iff` gives `ψ` vanishing on forbidden flags;
   `exists_constrained_flagSeq_limit` ([`ConstrainedRep`](./ConstrainedRep.lean)) gives a sequence
   of **forbidden-free** flags converging to `ψ`. Pick a term `G_t` with base size `n = |G_t|`
   large (so `1 − ρ_∞(n) < ε/2` on every `Fi`, via `rho_inf_tendsto_one`) and with
   `|p(Fi, G_t) − ψ.val Fi| < ε/10`. By `mem_of_forbiddenFree`, `G_t` is **in the class**; let
   `θ = G_t.type_embed : σ ↪g G_t.graph`.

3. **Blow up and take a limit.** `exists_blowup_limit` ([`BlowupSequence`](./BlowupSequence.lean))
   gives the uniform `(M+1)`-blow-up sequence `B_M` of `G_t.graph` and a subsequential limit `φ₀`.
   Since each `B_M` is in the class (`clone_closed`), `blowup_limit_mem_Q0` gives
   `posHomPoint φ₀ ∈ Q0`, and `blowup_limit_type_pos` gives `φ₀⟨σ⟩₀ > 0` — so `ℙ[φ₀]` exists and
   `φ₀` indexes the `S_σ` union.

4. **Weak convergence.** The σ-rooting measures `P_M = B_M.toProbMeasureSeq` converge weakly to
   `(ℙ[φ₀]).map Subtype.val` on `FlagDensitySpace σ` (`tendsto_rootingMeasure_extend`,
   [`WeakConvergence`](./WeakConvergence.lean)).

5. **Cylinder mass `P_M(C̃) ≥ c` (the crux, `planted_cylinder_mass`).** Let `C̃` be the closed
   cylinder centred at the *base* density profile, radius `δ`. By
   `toProbMeasure_apply_eq_labeling_ratio` ([`RootingUniform`](./RootingUniform.lean)),
   `P_M(C̃) = #{labelings with profile ∈ C̃}/#{labelings}`; the labelings biject with
   `blowupEmbeddings` (via `card_labelings_eq_card_embeddings` + the host-equiv isos). Each
   **planted** embedding `⟨θ·,c·⟩` corresponds to `blowupLabeledGraph m θ c`, whose density is
   within `1 − ρ(n,M) < δ` of the base (`planted_estimate` + `rho_tendsto_atTop`), so its profile
   lands in `C̃`. Hence `P_M(C̃) ≥ #plantedEmbeddings/#blowupEmbeddings ≥ (1/2n)^{n₀} =: c > 0`
   (`planted_mass` with `λ = n₀/n`), uniformly for all large `M`.

6. **Portmanteau + support.** Closed-set Portmanteau
   (`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`) turns `P_M(C̃) ≥ c` into
   `(ℙ[φ₀]).map val (C̃) ≥ c`, i.e. `ℙ[φ₀](C̃ ∩ X_σ) ≥ c > 0`. A positive-measure closed set meets
   the support (`Measure.measure_compl_support`), so `supp ℙ[φ₀]` contains a point of the cylinder
   — which (ε-split: `≤ ε/2` to the base, `< ε/10` base-to-`ψ`) lies in the target neighbourhood
   of `ψ`. Therefore the neighbourhood meets `A`, and `ψ ∈ S_σ`. ∎

`cor:clique-free` is then `clone_root_plantable (cliqueFreeClass r) σ`, with
`clique_free_quotient_iff_ensemble` recovering the quotient/ensemble equivalence via
`support_criterion`.
