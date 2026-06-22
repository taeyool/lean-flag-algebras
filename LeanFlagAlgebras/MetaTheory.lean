import LeanFlagAlgebras.MetaTheory.MeasureSupport
import LeanFlagAlgebras.MetaTheory.EvalAlgebra
import LeanFlagAlgebras.MetaTheory.ConstrainedClass
import LeanFlagAlgebras.MetaTheory.SupportClosure
import LeanFlagAlgebras.MetaTheory.Blowup
import LeanFlagAlgebras.MetaTheory.ProductTV
import LeanFlagAlgebras.MetaTheory.DensityBridge
import LeanFlagAlgebras.MetaTheory.LabeledCount
import LeanFlagAlgebras.MetaTheory.BlowupFlag
import LeanFlagAlgebras.MetaTheory.MeasureUniqueness
import LeanFlagAlgebras.MetaTheory.CloneCount
import LeanFlagAlgebras.MetaTheory.PlantedCount
import LeanFlagAlgebras.MetaTheory.CloneTotal
import LeanFlagAlgebras.MetaTheory.PlantedEstimate
import LeanFlagAlgebras.MetaTheory.ForbiddenIdeal
import LeanFlagAlgebras.MetaTheory.ConstrainedRep
import LeanFlagAlgebras.MetaTheory.InducedContainment
import LeanFlagAlgebras.MetaTheory.HeredClass
import LeanFlagAlgebras.MetaTheory.GraphClassConstraint
import LeanFlagAlgebras.MetaTheory.BinomialRatio
import LeanFlagAlgebras.MetaTheory.WeakConvergence
import LeanFlagAlgebras.MetaTheory.RootingUniform
import LeanFlagAlgebras.MetaTheory.BlowupSequence
import LeanFlagAlgebras.MetaTheory.CapstoneShared
import LeanFlagAlgebras.MetaTheory.CloneClosed
import LeanFlagAlgebras.MetaTheory.SubstitutionBlowup
import LeanFlagAlgebras.MetaTheory.SubstitutionEstimate
import LeanFlagAlgebras.MetaTheory.SubstitutionSequence
import LeanFlagAlgebras.MetaTheory.SubstitutionClosed
import LeanFlagAlgebras.MetaTheory.BlowupClosed
import LeanFlagAlgebras.MetaTheory.TrueClone
import LeanFlagAlgebras.MetaTheory.Substitution
import LeanFlagAlgebras.MetaTheory.ClusterGraph
import LeanFlagAlgebras.MetaTheory.C5Free
import LeanFlagAlgebras.MetaTheory.FinitePlanting
import LeanFlagAlgebras.MetaTheory.SparseRootRepair
import LeanFlagAlgebras.MetaTheory.C5OneRoot
import LeanFlagAlgebras.MetaTheory.C5TwoRootNonEdge
import LeanFlagAlgebras.MetaTheory.C5Blowup
import LeanFlagAlgebras.MetaTheory.Pinning

/-! # Meta-theory of flag algebras (`MetaTheory/paper.tex`)

Formalisation of the proved results in §1–8 of `MetaTheory/paper.tex`, plus §9's abstract
pinning obstruction: when forbidden-subgraph ("quotient") reasoning is *complete* for a
constrained graph class, and when it can fail.

Aggregator. Currently wires in:

* `MeasureSupport`  — §2 `lem:support-as` (almost-sure non-negativity ↔ non-negativity on the
  support of a measure).
* `EvalAlgebra`     — flag-algebra evaluations as a Stone–Weierstrass-dense subalgebra of
  `C(X_σ)` (used by §4 and, later, §5).
* `ConstrainedClass`— §3: the forbidden ideal, the quotient algebra `A^σ[T₁]`, and the
  supported space `Q_σ` with its intrinsic description `mem_Qσ_iff` and closedness.
* `SupportClosure`  — §2 `lem:support-passes-general` and §4 `def:root-planting` +
  `thm:support-criterion` (the support-closure criterion).
* `Blowup`          — §5 `def:independent-blow-up`: the independent blow-up construction, its
  projection, the preservation of `K_r`-freeness (the core of `cor:clique-free`), and
  `lem:planted-mass` (positive probability of the planted root).
* `ProductTV`       — the product-distribution total-variation bound
  (`eq:good-unnormalized-weight-bound`), the analytic core of `lem:planted-estimate`.
* `DensityBridge`   — the entry point of the density bridge: `flagDensity₁ F G` exposed as the
  card ratio `labeledGraphCount F G / ((|G|−k) choose (|F|−k))`.
* `LabeledCount`    — `labeledGraphCount_eq_subset_count` and `flagDensity₁_eq_subset_count_div`:
  flag density as the fraction of vertex subsets inducing a copy of the flag.
* `BlowupFlag`      — the blow-up/base as labelled graphs, and `blowupGoodIso`: on a good vertex
  set the induced labelled subgraph of the blow-up is `≃f` (via projection) that of the base.
* `MeasureUniqueness` — `measure_eq_of_integral_flag_eq`: a probability measure on `X_σ` is
  determined by its flag-integrals (the weak-limit uniqueness used in `thm:clone-root-plantable`).
* `CloneCount`       — `clone_fiber_card`: subsets of the blow-up projecting injectively onto a
  base set `W` number `∏_{v∈W} m v` (the clone multiplicity in the good-event count).
* `PlantedCount`     — `good_event_count`: the good blow-up subsets inducing `F₀` are counted
  fiberwise as `∑_W ∏_{v∈W∖roots} m v` over the base subsets `W` inducing `F₀`.
* `CloneTotal`       — `clone_total_card`/`clone_total_card_const`: the total good size-`r`
  supersets of the roots, `C(|S₀|,r)·∏ m v` (equal clones: `C(|S₀|,r)·M^r`).
* `PlantedEstimate`  — §5 `lem:planted-estimate` (equal non-root clones): `planted_estimate`, the
  density of `F₀` in the planted blow-up differs from its density in the base by at most `1 − ρ`,
  `ρ = M^(ℓ−k)·C(n−k,ℓ−k)/C(N−k,ℓ−k)` (`N = ∑ v, m v`). The good/bad split: the good-event count
  collapses to `M^(ℓ−k)·#{base subsets inducing F₀}`, the bad count is bounded by the size-ℓ
  superset total, and a little rational algebra yields the bound.
* `ForbiddenIdeal`   — §3 faithfulness `forbiddenIdeal_eq_span`: under heredity (the product of a
  forbidden flag with any element stays in the ℝ-span of the forbidden flags), the forbidden
  ideal coincides with that ℝ-span.
* `ConstrainedRep`   — the constrained representation theorem `exists_constrained_flagSeq_limit`
  (constrained refinement of Razborov 3.3(b)): a positive homomorphism vanishing on every
  forbidden flag is the density limit of a flag sequence whose flags are themselves forbidden-free.
  The foundational input to `thm:clone-root-plantable`.
* `InducedContainment` — the density/containment bridge: a positive flag-density yields an inducing
  vertex subset (`exists_inducing_subset_of_flagDensity₁_ne_zero`) and, for unlabelled flags, an
  induced graph embedding `D.graph ↪g H.graph` (`exists_graph_embedding_of_flagDensity₁_ne_zero`).
* `HeredClass`        — the shared class framework (used by §5, §6 and §7): `graphFlag`, the
  closure-free `HeredClass` structure (`Mem` + `comap` heredity), its `Constraint` (`constraintOf`),
  and the two capstone-consumption lemmas `mem_of_forbiddenFree` (forbidden-free ⟹ in class, via
  `flagDensity_self`) and `forbiddenFree_of_mem` (in class ⟹ forbidden-free, via the containment
  bridge + `comap`). These never use any closure operation, so they serve every constrained class.
* `GraphClassConstraint` — the §5 clone-closure layer: `GraphClass extends HeredClass` adding
  `clone_closed` (closure under independent blow-ups), thin wrappers over the `HeredClass`
  constraint/consumption lemmas, and the `K_r`-free instance `cliqueFreeClass`.

* `BinomialRatio`    — the analytic core of the planted limit under uniform clone sizes:
  `rho_tendsto_atTop` (`M^(ℓ−k)·C(n−k,ℓ−k)/C(nM−k,ℓ−k) → descFactorial(n−k,ℓ−k)/n^(ℓ−k)` as
  `M→∞`) and `rho_inf_tendsto_one` (that limit `→ 1` as `n→∞`).
* `WeakConvergence`  — `tendsto_rootingMeasure_extend`: the σ-rooting measures of *any* flag
  sequence converging to `φ₀` converge weakly (on `FlagDensitySpace σ`) to the inclusion-
  pushforward `(ℙ[φ₀]).map Subtype.val` of the random extension (subsequence-uniqueness via the
  existing integral identification + `measure_eq_of_integral_flag_eq`).

* `RootingUniform`   — the σ-rooting measure is the uniform-over-rootings pushforward:
  `toProbMeasure_apply_eq_dnf_ratio` (the measure of a set is the `downwardNormalizingFactor`
  ratio over labelings whose density profile lands in the set) and
  `sum_isomorphismCount_labelExtensions` (`∑ isomorphismCount = #σ-rootings of the host graph`).
  Together: rooting-measure(A) = `#{rootings with profile ∈ A} / #{rootings}` — the bridge that
  turns `lem:planted-mass` (an embedding ratio) into a measure lower bound.
* `BlowupSequence`   — part (2) of the capstone: the uniform `(M+1)`-blow-up flag sequence
  `blowupFlagSeq` (presented on `Fin (n·(M+1))` via `blowupGraphFin`), its subsequential limit
  `exists_blowup_limit`, and the two properties `blowup_limit_mem_Q0` (`posHomPoint φ₀ ∈ Q0`, via
  `forbiddenFree_of_mem` + `clone_closed`) and `blowup_limit_type_pos` (`φ₀⟨σ⟩₀ > 0`, from the
  `1/nⁿ⁰` σ-type density lower bound surviving the blow-up).

* `CapstoneShared`   — the construction-agnostic capstone toolkit shared by the §5 and §6–§7
  root-plantability finales (and reusable for §8+): the σ-rooting-measure-as-labelling-count identity
  (`toProbMeasure_apply_eq_labeling_ratio`), closed coordinate cylinders (`cyl`/`isClosed_cyl`), the
  finite-cylinder closure criterion (`mem_closure_of_forall_finset_cylinder`), the asymptotic
  planted-gap `rhoInf`, and the σ-labelling/embedding counting isos. None of it mentions a blow-up.
* `CloneClosed`      — §5 finale. `clone_root_plantable` (`thm:clone-root-plantable`): every
  clone-closed hereditary `GraphClass` is root-plantable, `Sσ = Qσ`. The reverse inclusion
  `Qσ ⊆ Sσ` assembles: the constrained representation (in-class base flag `G_t`), the uniform
  blow-up limit `φ₀ ∈ Q0` with `φ₀⟨σ⟩₀ > 0`, weak convergence of the rooting measures to
  `ℙ[φ₀]`, closed-set Portmanteau, and the cylinder-mass bound `P_M(C̃) ≥ (1/2n)ⁿ⁰` (`RootingUniform`
  turns the rooting measure into a labeling/embedding count, `planted_estimate`+`BinomialRatio`
  put the planted rootings in the cylinder, `lem:planted-mass` lower-bounds the count). Then
  `clique_free_root_plantable`/`clique_free_quotient_iff_ensemble` (`cor:clique-free`, from
  `cliqueFreeClass`): the `K_r`-free (and triangle-free, `r = 3`) classes are root-plantable, so
  quotient and ensemble semantics agree for every `f`.

This completes the §1–5 layer.

§6–§7 build on the §5 machinery by generalising the independent blow-up to the **generalised
blow-up** `subBlowup G W` (a within-class family `W`), which covers the complete blow-up of §6
(`W = ⊤`, clique clone classes) and the substitution of §7 (`W = H_v`, arbitrary in-class fibres).
Off the diagonal the adjacency is the base adjacency `G`, so on the "good" (transversal) sets the
whole §5 estimate machinery applies unchanged.

* `SubstitutionBlowup` — `subBlowup`/`completeBlowup`, off-diagonal agreement, the planted labelled
  graph, and `good_event_induces_iff_sub` (the §5 good-event isomorphism, carried across the
  identity-on-a-transversal iso `subBlowupToIndepIso`).
* `SubstitutionEstimate` — `planted_mass_sub` and `planted_estimate_sub` (§6 `lem:true-planted-estimate`
  / §7 `lem:general-planting-estimate`); the estimate is `PlantedEstimate.planted_estimate_host`
  (the host-parametric form of `lem:planted-estimate`) at `B = subBlowupLabeledGraph`.
  The §6–§7 classes reuse the closure-free `HeredClass` base directly (cluster graphs are a
  `HeredClass` that is *not* a `GraphClass`), and the capstone reuses `CapstoneShared` — so the
  §6–§7 layer does not import the §5 capstone `CloneClosed`.
* `SubstitutionSequence` — the uniform generalised-blow-up flag sequence and its base limit `φ₀`
  (`blowup_limit_mem_Q0_sub`, `blowup_limit_type_pos_sub`).
* `SubstitutionClosed` — `subst_root_plantable`: under a uniform within-class blow-up closure
  hypothesis, `S_σ = Q_σ` (the §6–§7 capstone engine, the analogue of `clone_root_plantable`).
* `BlowupClosed` — **the §7 unification.** The single-vertex blow-up `oneBlowup G v H`
  (`def:vertex-blowup`), the blow-up-closure property `BlowupClosed` (`def:blow-up-closed`), the
  iteration bridge `BlowupClosed.toUniform` (`lem:blowup-iterate`), and the unified theorem
  `blowupClosed_root_plantable` (`thm:blowup-root-plantable`): every blow-up-closed hereditary class
  is root-plantable. Clone-, true-clone- and substitution-closure are special cases
  (`…toBlowupClosed`), so the three theorems below are corollaries.
* `TrueClone` — §6 `thm:true-clone-root-plantable`: `true_clone_root_plantable` (corollary of
  `blowupClosed_root_plantable` via `TrueCloneClosed.toBlowupClosed`, clique interior).
* `Substitution` — §7 `thm:substitution-root-plantable`: `substitution_root_plantable` (corollary
  via `SubstitutionClosed.toBlowupClosed`); `rem:strictness` — substitution-closure is strictly
  stronger than blow-up-closure and misses §5/§6.
* `ClusterGraph` — §6 `cor:cluster-graphs`: cluster graphs (`P₃`-free) are true-clone-closed, hence
  `cluster_root_plantable` — root-plantable though *not* clone-closed (nor substitution-closed).

§8 adds a *finite, local* root-plantability criterion that applies beyond any global blow-up closure,
and verifies it for the (dense, not blow-up-closed) `C₅`-free class by a sparse local repair.

* `FinitePlanting` — §8 `def:finite-local-planting` + `thm:finite-local-planting`:
  `finitePlanting_root_plantable` — the **finite planting property** at a non-degenerate `σ` implies
  root-plantability (`S_σ = Q_σ`). The §5/§7 capstone argument with the blow-up sequence replaced by
  the abstract planting family `Hₜ`; reuses `CapstoneShared`/`WeakConvergence`/`SupportClosure`
  verbatim, and a generic `flagSeqLimit_mem_Q0`.
* `SparseRootRepair` — §8 `def:sparse-root-repair` + `thm:sparse-repair-planting`:
  `sparseRootRepair_finitePlanting` — sparse root-blow-up repairs imply finite planting, via a
  coupling-free combinatorial sampling estimate (`counting_coupling_bound`).
* `C5Free` — the `C₅`-free hereditary class `c5FreeClass` (Mathlib `IsContained`/`Free`), and §8
  `lem:c5-nbhd` (`c5free_neighborhood_edge_card_le`): `e(G[N(v)]) ≤ |N(v)|` (`P₄`-free neighbourhoods).
* `C5OneRoot` — §8 `def:c5-one-root-planting`/`lem:c5-planting-free`/`thm:c5-one-root`: the one-root
  planting `oneRootPlant`, its `C₅`-freeness (`oneRootPlant_c5free`), and `c5free_one_root_plantable`
  (`S₁ = Q₁` for the `C₅`-free class at the one-vertex type).
* `C5TwoRootNonEdge` — §8 two-root non-edge analogues: `twoRootPlant`, `twoRootPlant_c5free`, and
  `c5free_two_root_nonedge_plantable` (`S_η = Q_η`).
* `C5Blowup` — §8 `lem:c5-blowup`: an independent blow-up of a `C₅`-free graph is `C₅`-free iff the
  graph is triangle-free (`c5_blowup_free_iff_triangleFree`) — why naive blow-ups fail for `C₅`-free.
* `Pinning` — §9 `thm:pinning`: a labelled quantity pinned almost surely to one value on all
  admissible ensembles, but taking a different value at some quotient point, obstructs
  root-plantability (`pinning_obstruction`).
-/
