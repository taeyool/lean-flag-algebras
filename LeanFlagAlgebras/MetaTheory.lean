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
import LeanFlagAlgebras.MetaTheory.EdgeObstruction
import LeanFlagAlgebras.MetaTheory.StarWitness
import LeanFlagAlgebras.MetaTheory.C4Free
import LeanFlagAlgebras.MetaTheory.DegenerateFamily
import LeanFlagAlgebras.MetaTheory.DenseObstruction
import LeanFlagAlgebras.MetaTheory.FlagComplement
import LeanFlagAlgebras.MetaTheory.ComplementHom
import LeanFlagAlgebras.MetaTheory.ComplementClass
import LeanFlagAlgebras.MetaTheory.ComplementInvariance
import LeanFlagAlgebras.MetaTheory.C5FewTriangles
import LeanFlagAlgebras.MetaTheory.C5EdgeObstruction
import LeanFlagAlgebras.MetaTheory.NoInterior
import LeanFlagAlgebras.MetaTheory.EdgeThinning
import LeanFlagAlgebras.MetaTheory.EdgeThinningLimit
import LeanFlagAlgebras.MetaTheory.NoInteriorThinning
import LeanFlagAlgebras.MetaTheory.DownwardAverage
import LeanFlagAlgebras.MetaTheory.EmptyTypeCollapse
import LeanFlagAlgebras.MetaTheory.CertificateCones
import LeanFlagAlgebras.MetaTheory.VanishingIdeal
import LeanFlagAlgebras.MetaTheory.BooleanPoint
import LeanFlagAlgebras.MetaTheory.SinglePoint
import LeanFlagAlgebras.MetaTheory.C5EdgeInert
import LeanFlagAlgebras.MetaTheory.RelativeSupport
import LeanFlagAlgebras.MetaTheory.RelativeClosure
import LeanFlagAlgebras.MetaTheory.RelativeSlackness
import LeanFlagAlgebras.MetaTheory.KernelSlackness
import LeanFlagAlgebras.MetaTheory.RelativePlanted
import LeanFlagAlgebras.MetaTheory.RelativeCertificateGap
import LeanFlagAlgebras.MetaTheory.RelativePositivstellensatz
import LeanFlagAlgebras.MetaTheory.CertificateSliceVanishing
import LeanFlagAlgebras.MetaTheory.ParametricP4Slice
import LeanFlagAlgebras.MetaTheory.TuranLimit
import LeanFlagAlgebras.MetaTheory.MantelNotPlantable
import LeanFlagAlgebras.MetaTheory.SliceRecovery
import LeanFlagAlgebras.MetaTheory.GraphonBasic
import LeanFlagAlgebras.MetaTheory.GraphonMoments
import LeanFlagAlgebras.MetaTheory.GraphonRigidity
import LeanFlagAlgebras.MetaTheory.GraphonQuantStability
import LeanFlagAlgebras.MetaTheory.TuranAut
import LeanFlagAlgebras.MetaTheory.TuranDirac
import LeanFlagAlgebras.MetaTheory.TuranSliceIdentities
import LeanFlagAlgebras.MetaTheory.GraphonInducedDensity
import LeanFlagAlgebras.MetaTheory.PairSubsetCount
import LeanFlagAlgebras.MetaTheory.EmptyTypeGraphBridge
import LeanFlagAlgebras.MetaTheory.GraphonHom
import LeanFlagAlgebras.MetaTheory.StdRootedBridge
import LeanFlagAlgebras.MetaTheory.GraphonRootedDensity
import LeanFlagAlgebras.MetaTheory.GraphonRootedHom
import LeanFlagAlgebras.MetaTheory.GraphonRootedMeasure
import LeanFlagAlgebras.MetaTheory.GraphonKernelTransport
import LeanFlagAlgebras.MetaTheory.GraphonStep
import LeanFlagAlgebras.MetaTheory.GraphonCounting
import LeanFlagAlgebras.MetaTheory.GraphonRepresentation
import LeanFlagAlgebras.MetaTheory.GraphonParametricTransport
import LeanFlagAlgebras.MetaTheory.ParametricStabilityModulus

/-! # Meta-theory of flag algebras (`MetaTheory/paper.tex`)

Formalisation of the proved results in §1–10 and §11.2–§11.8 of `MetaTheory/paper.tex`: when
forbidden-subgraph ("quotient") reasoning is *complete* for a constrained graph class, when it
can fail, and the relative (slice) theory that strengthens it by further constraints.

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

§9.1–§9.2 instantiate the obstruction concretely.  The mechanism is **boundary pinning** of the
one-root edge flag `e` at the one-vertex type `vtype`: its density is pinned almost surely to a
boundary value of `[0,1]` (`0` for a degenerate class, `1` for a co-degenerate one) across every
admissible random extension, while the constrained quotient still contains a labelled limit (a star,
resp. co-star) attaining the opposite boundary.

* `EdgeObstruction` — §9 the one-root edge flag `e` / unlabelled edge `ρ = ⟦e⟧₀`, `def:edge-degenerate`
  (`EdgeDegenerate`) and its dual `CoEdgeDegenerate`, the two endpoint a.s.-pinning facts
  (`ae_e_eq_zero_of_pinned`/`ae_e_eq_one_of_pinned`, from the expectation `∫ χ e = φ₀ ρ`), and the
  abstract obstruction theorems `edgeDegenerate_not_rootPlantable_of_witness` /
  `coEdgeDegenerate_not_rootPlantable_of_witness` (over `pinning_obstruction`).
* `StarWitness` — §9 the concrete witnesses: a flag-sequence-to-`Q_vtype` assembly
  (`exists_Qσ_point_edge_eq`, via Razborov 3.3(a)), the star / co-star constructions with their
  one-root edge densities (`star_edge_density = 1`, `coStar_edge_density = 0`), and
  `thm:degenerate-obstruction` (`degenerate_not_rootPlantable`) + `cor:codegenerate`
  (`coDegenerate_not_rootPlantable`).
* `C4Free` — §9.1 the `C₄`-free class `c4FreeClass`, the elementary Kővári–Sós–Turán bound
  `(2·e(G))² ≤ 2|G|³` (`c4free_card_edges_sq_le`, cherry double-count), `lem:c4-edge-zero`
  (`c4FreeClass_edgeDegenerate`) and `cor:c4-counterexample` (`c4free_not_rootPlantable`).
* `DegenerateFamily` — §9.1 the general principle behind `cor:degenerate-family`:
  `edgeDegenerate_of_subquadratic` (a subquadratic edge bound `e(G) ≤ f(|G|)`, `f N / N² → 0`, implies
  edge-degeneracy).  The four listed families are instances via their extremal bounds.
* `DenseObstruction` — §9.2 `cor:codegenerate` made concrete: the *dense* complement-of-`C₄`-free
  class `coC4FreeClass` (edge density → 1) is also not root-plantable (`coC4free_not_rootPlantable`),
  via `coC4FreeClass_coEdgeDegenerate` — density is not the dividing line.  Uses complementation only
  through the edge-count identity `e(G)+e(Gᶜ)=C(|G|,2)` and `coStarᶜ = star`, not the full
  `lem:complementation` isomorphism.

§9.2 `lem:complementation` (the full **complementation invariance** of root-plantability) is
formalised in a four-module stack, via the complement *homeomorphism* of homomorphism spaces rather
than the paper's explicit flag-algebra complement isomorphism (a documented proof-route deviation):

* `FlagComplement` — the complement on flags (`Flag.compl : Flag σ V → Flag σᶜ V`, with the clean
  `uncompl` involution partner) and the combinatorial core `flagDensity₁_compl` /`flagDensity₂_compl`
  (`flagDensity Fᶜ Gᶜ = flagDensity F G`), `unlabel_compl`, `downwardNormalizingFactor_compl`.
* `ComplementHom` — `complHom : PositiveHom σ → PositiveHom σᶜ` (built from the density profile via
  `positiveHomFromZeroSpaceOneMulProp`, the props transferred through the density identities), its
  inverse `uncomplHom`, and the homeomorphism `complHomeo : PositiveHomSpace σ ≃ₜ PositiveHomSpace σᶜ`.
* `ComplementClass` — the complement hereditary class `HeredClass.compl` (`K̄`, `Mem G := Mem Gᶜ`),
  the forbidden-flag correspondence, and `complHomeo_image_Qσ` (`Φ '' Q_σ(K) = Q_{σᶜ}(K̄)`).
* `ComplementInvariance` — the measure pushforward `complHomeo_map_eq` (`Φ_* ℙ[φ₀] = ℙ[φ̄₀]`, via
  `measure_eq_of_integral_flag_eq`), the support transfer `complHomeo_image_Sσ`, and the capstone
  `complementation_invariance` (`lem:complementation`): `RootPlantable (K.constraintOf σ) ↔
  RootPlantable (K̄.constraintOf σᶜ)`, with `complementation_invariance_oneVertex` the `σ = vtype`
  corollary.

§9.5 is the **`C₅`-free edge-type obstruction** — the first dense, non-blow-up-closed class for which
the question is nontrivial, and the section that refutes the natural all-types `C₅`-free conjecture.
Root-plantability holds for a single root and for a non-adjacent pair (§8) but *fails* at the two-root
**edge** type, where a book graph obstructs it.

* `C5FewTriangles` — §9.5 `lem:c5-few-triangles`: `3·T(G) ≤ 2·e(G)` for `C₅`-free `G`
  (`c5free_three_mul_triangle_le`, via `3·T(G) = ∑_v e(G[N(v)]) ≤ ∑_v deg(v)` using `lem:c5-nbhd`),
  the unlabelled-triangle density `T(G)/C(N,3)` (`flagDensity_unlabelledTriangle_eq`), and the
  triangle-degeneracy `c5FreeClass_triangleDensity_zero` (every constrained limit has triangle
  density `0`; mirror of `c4FreeClass_edgeDegenerate`).
* `C5EdgeObstruction` — §9.5 the two-root edge type `edgeType` (`τ`), the common-neighbour triangle
  flag `F_tri` (`F_△`), and the obstruction: `ae_Ftri_eq_zero_of_pinned` (`cor:c5-edge-pinned`, `F_△`
  pinned a.s. to `0` under random edge-rooting), the book graph `bookLabeled` (`def:c5-book`) with
  `book_c5free` (`lem:c5-book` freeness) and `book_Ftri_density = 1`, the quotient point
  `exists_book_Qτ_point` (`lem:c5-book`), and the capstone `c5free_edge_not_rootPlantable`
  (`thm:c5-edge-not-root-plantable`) via `pinning_obstruction`. `cor:c5-no-pin` records that the
  one-vertex type gives no obstruction: `c5free_triOverVtype_zero_on_Qvtype` (the one-root triangle
  flag is `0` on all of `Q_vtype`) and `c5free_edge_not_pinned` (the edge flag takes a.s. values `0`
  on edgeless limits and `≥ 1/4` on balanced complete bipartite limits — not pinned).  A generalised
  quotient-point assembly `exists_Qσ_point_flag_eq` (any `σ`, any flag) is also provided.

§9.4 is **boundary pinning** (`thm:no-interior`): for an *edge-deletion-closed* hereditary class, no
*interior* density value is ever pinned, so every pinning obstruction is a boundary one.  The proof
exhibits a `{0,1}`-valued point of `S_σ` — the `λ → 0` limit of random extensions of edge-thinned
constrained limits.

* `NoInterior` — the low-level predicate `EdgeDeletionClosed` (every spanning subgraph of an in-class
  graph is in-class), shared by the thinning stack.
* `EdgeThinning` — the random edge-thinning of a finite graph (Bernoulli `Measure.pi` over potential
  edges): `thinExpectDensity` (the expected induced density), its first-moment upper bound
  `thinExpectDensity_le_pow` (`≤ C(C(|M|,2),e(M))·λ^{e(M)}`, the correct *induced*-density form) and
  σ-type lower bound `thinExpectDensity_type_ge` (`≥ λ^{e(σ)}·density`), and the second-moment
  realization `exists_thinned_realization` (a deterministic in-class spanning subgraph whose densities
  track the expectations within `ε`, via a block-independence variance bound + Chebyshev + union
  bound).
* `EdgeThinningLimit` — `exists_thinned_limit`: the edge-thinned constrained limit `φ₀^λ ∈ Q₀`
  (a diagonal realization of `exists_thinned_realization` over a representing sequence), with
  `φ₀^λ⟨σ⟩₀ ≥ λ^{e(σ)}·φ₀⟨σ⟩₀ > 0` and the per-flag bound `φ₀^λ(M) ≤ C·λ^{e(M)}`.
* `NoInteriorThinning` — `exists_boolean_point_in_Sσ`: as `λ → 0`, the flag moments of `ℙ[φ₀^λ]`
  converge to the `{0,1}`-valued "edgeless cloud" profile (new-edge flags vanish like `λ`, the unique
  edgeless extension of each size `→ 1`), so an L¹/Markov cylinder argument places that boolean point
  `ψ_σ ∈ S_σ`; hence the capstone `no_interior_pinning` (`thm:no-interior`): a `σ`-flag pinned to `c`
  on `S_σ` has `c ∈ {0,1}`.

§10 is **the gap is invisible to density bounds** (`sec:empty-type`, Prop 64–Cor 70): the §9
obstructions never affect an actual empty-type density bound — the two semantics coincide at the
empty type, and the witnesses that expose the gap unlabel to zero.

* `DownwardAverage` — the §10 engine: the `posHomPoint`/`toPosHom` roundtrips, the unlabelling
  weight is a probability (`downwardNormalizingFactor_le_one`, so `φ₀ ⟦1⟧₀ ∈ [0,1]`), degenerate
  base limits kill every unlabelled average (`downward_eval_eq_zero_of_degenerate`), the **master
  evaluation bound** `abs_downward_eval_le_of_abs_le_on_Sσ` (`|s| ≤ δ` on `S_σ` ⟹ `|φ₀ ⟦s⟧₀| ≤ δ`
  on `Q₀`), and the singleton collapse `downward_eval_eq_of_Sσ_singleton`.
* `EmptyTypeCollapse` — §10 `prop:empty-type` + `cor:confined`: the empty-type extension is Dirac
  (`extend_emptyType_eq_dirac`, via the moment-uniqueness theorem `measure_eq_of_integral_flag_eq`
  and `downward_emptyType`), `S_∅ = Q₀` (`Sσ_emptyType_eq`), the empty type is always
  root-plantable (`emptyType_rootPlantable`, `heredClass_emptyType_rootPlantable`), and the two
  semantics coincide on `A⁰` (`emptyType_quotient_iff_ensemble`,
  `ensemble_implies_quotient_emptyType`).
* `CertificateCones` — §10 `thm:no-closed-certificate-gap`: the quotient cone `quotCone`
  (unlabelled averages of sums of squares) and the ensemble cone `ensCone` (of elements
  non-negative on `S_σ`) have the same closure in the `Q₀`-seminorm (`Q0Within`/`MemQ0Closure`);
  the crux `ensCone_subset_closure_quotCone` approximates `√(max(s,0))` by a flag evaluation
  (Stone–Weierstrass `exists_flag_near`) and squares it; the equality `no_closed_certificate_gap`
  holds for every type — no non-degeneracy needed.
* `VanishingIdeal` — §10 `prop:ideal-zero`: elements vanishing on `S_σ` unlabel to zero on `Q₀`
  (`downward_eval_eq_zero_of_zero_on_Sσ`), an ideal (`downward_mul_eval_eq_zero_of_zero_on_Sσ`);
  pinning witnesses `g − c•1` and their flag-multiples unlabel to zero
  (`pinned_witness_downward_eq_zero`); equal evaluations on `S_σ` give equal averages
  (`downward_eval_congr_of_eqOn_Sσ`).
* `BooleanPoint` — the labelled empty-graph limit `edgelessPoint` and complete-graph limit
  `completePoint` in `X_vtype`: the `IsEdgelessFlag`/`IsCompleteFlag` predicates, per-size
  uniqueness of the edgeless/complete flag, existence via rooted flag-sequence limits, and the
  boolean-profile workhorse `val_eq_boolean_of_nonEdgeless_zero` (vanishing pattern ⟹ full
  profile, by size-`n` sum-to-one), with the uniqueness lemmas
  `eq_edgelessPoint_of_nonEdgeless_zero` / `eq_completePoint_of_nonComplete_zero`.
* `SinglePoint` — §10 `prop:single-point`: for an edge-degenerate class every edge-containing
  unlabelled flag dies (`eval_eq_zero_of_edgeDegenerate`, expanding the 2-vertex edge flag), so
  all non-edgeless `vtype`-flags vanish a.s. and `S_vtype = {edgelessPoint}`
  (`Sσ_eq_singleton_of_edgeDegenerate`); dually `S_vtype = {completePoint}` for a
  co-edge-degenerate class (direct mirror — not via `lem:complementation`).  Both certificate
  cones collapse to the ray `ℝ≥0·1₀` (`edgeDegenerate_cone_collapse`,
  `coEdgeDegenerate_cone_collapse`, `smul_one_mem_quotCone_vtype`): the §9 degeneracy
  counterexamples cost nothing for density bounds.
* `C5EdgeInert` — §10 `cor:c5-edge-closed-inert`: the `C₅`-free edge-type gap is closed-cone
  inert (`c5free_edge_no_closed_certificate_gap`); the pinned witness `F_△` vanishes on all of
  `S_τ` (`c5free_Ftri_zero_on_Sσ`) and, with every flag-multiple, unlabels to zero
  (`c5free_Ftri_mul_downward_eq_zero`).
* `RelativeSupport` — §11.2 relative ensemble semantics: the relative support `relSσ Y σ`
  (= `S_σ(Y)`), relative soundness (`prop:relative-soundness`, `relative_soundness`), the
  unconditional relative support-closure criterion (`prop:relative-criterion`,
  `relative_criterion`), and `Y = Q₀` recovery of the absolute theory (`Sσ_eq_relSσ`).
* `RelativeClosure` — §11.2 `lem:relative-closure` (`relSσ_closure_eq`): closing the constraint
  set does not change the relative support; via weak continuity of the random extension
  (`extend_tendsto`) and support lower-semicontinuity along weak convergence
  (`support_subset_closure_iUnion_support`).
* `RelativeSlackness` — §11.3 `thm:relative-slackness` (the `relative_slackness_*` family:
  soundness, approximate, exact, and global vanishing), `lem:relative-cauchy-schwarz`
  (`downward_cauchy_schwarz`), `cor:sos-first-moments`
  (`certificate_first_moment_sq_bound(_one)`), and `prop:unique-slice-stability`
  (`unique_slice_stability`).
* `KernelSlackness` — §11.3 `thm:kernel-slackness` (the `kernel_slackness_*` family): the
  matrix form of complementary slackness consuming a PSD block certificate directly; on the
  equality slice the labelled moment vector falls into `ker Q` (a.s. and on all of `S_σ(Y)`).
* `RelativePlanted` — §11.4 `def:relative-plantability` + `prop:relative-plantability`: the
  relative planted set `relQσ` (`Y`-planted views), relative root-plantability, closedness,
  `relSσ Y σ ⊆ relQσ hc Y σ ⊆ Qσ`, `Q_σ(Q₀) = Q_σ` (`relativelyRootPlantable_Q0_iff`), and the
  unconditional relative planted criterion (`relative_planted_criterion`).
* `RelativeCertificateGap` — §11.4 `thm:relative-certificate-gap`
  (`no_relative_closed_certificate_gap`): the quotient and relative-ensemble certificate cones
  have the same `‖·‖_Y`-closure over every slice.
* `RelativePositivstellensatz` — §11.4 `thm:relative-positivstellensatz`
  (`relative_positivstellensatz(_closure)`): non-negativity over an equality slice equals, up to
  `ε` and one squared-constraint penalty, non-negativity over the whole class.
* `CertificateSliceVanishing` — §11.6 `prop:equality-slice-vanishing` (`equality_slice_vanishing`)
  and the equality-slice construction `eqSlice`.
* `ParametricP4Slice` — §11.6 `thm:k4free-p4-equality-slice` + `thm:parametric-p4-equality-slice`:
  the verified `CompleteGraphFreeP4.gap_identity` certificate fed through relative slackness —
  the labelled slice equations at the non-edge/edge types (`parametricP4_eta_equation`,
  `parametricP4_tau_symm`, `parametricP4_tau_equation`, and the `k4freeP4_*` `r = 3` forms) and
  the extremal `K₄` density (`parametricP4_K4_density`; Zykov bound as explicit hypothesis).
* `TuranLimit` — §11.5, the existence half of `thm:turan-slice` / `thm:relative-mantel`: the
  Turán-graph flag sequence, its edge-density limit `(r-1)/r`, the balanced `r`-partite limit
  (`exists_turan_limit`), and nonemptiness of the Turán/Mantel slices.
* `MantelNotPlantable` — §11.4 `prop:mantel-not-plantable` (`mantel_not_relatively_plantable`):
  rooting at an isolated vertex added to `K_{n+1,n+1}` gives a Mantel-slice planted view with
  rooted edge density `0`, so `S_vtype(Y_Mantel) ⊊ Q_vtype(Y_Mantel)` (pinning input
  `thm:relative-mantel` (i) as explicit hypothesis).
* `SliceRecovery` — §11.7 `cor:parametric-p4-turan-recovery` (`parametric_recovery`) and the
  qualitative-stability corollaries (`parametric_qualitative_stability`,
  `k4free_qualitative_stability`), conditioned on the classical equality-case inputs.
* `GraphonBasic` — §11.7 preliminaries: graphons on `unitInterval`, the kernels `deg`/`codeg`,
  densities `p`/`D`/`T`, and the Fubini identities of the moment computations.
* `GraphonMoments` — §11.7 `thm:parametric-moments` (`moments_T`/`moments_D`/`moments_variance`/
  `moments_interval`/`moments_regular_iff`) and §11.8 `thm:approximate-moments`
  (`approximate_moments(_interval/_variance)`) — kernel-level, certificate-free.
* `GraphonRigidity` — §11.7 `thm:slice-rigidity` (`slice_rigidity`) + `cor:r3-rigidity`
  (`r3_rigidity`): the two local equations at the regular endpoint force the balanced complete
  `r`-partite graphon, in measurable-partition form.
* `GraphonQuantStability` — §11.8 `prop:k4free-p4-certificate-stability` /
  `thm:k4free-p4-quant-stability` / `thm:parametric-quant-stability` (kernel-level chains:
  `quadratic_confinement`, `interval_localisation`, the `r = 3` `Δ^{1/4}` edge-density
  stability, and `stability_via_modulus`).
* `TuranAut` — §11.5 supporting layer: Turán-graph automorphism transitivity on rooted
  patterns; all `σ`-labellings of a Turán flag are one flag class (`labelExtensions`
  subsingletons at the one-vertex, edge, and non-edge types).
* `TuranDirac` — §11.5 supporting layer: unique labellings make the finite rooting
  measures Dirac; weak convergence transfers Dirac-ness to the extension measure
  (`extend_eq_dirac_of_labelExtensions_subsingleton`), collapsing the relative support of
  a singleton constraint set (`relSσ_singleton_of_extend_dirac`); fixes the choice
  `turanLimit` of the balanced complete `r`-partite limit with its subsequence exposed.
* `TuranSliceIdentities` — §11.5 `thm:turan-slice` / `thm:relative-mantel`, the identity
  halves under the named Erdős–Simonovits hypothesis (`turan_slice_identity_vtype/_edge/
  _nonEdge`, `relative_mantel_vtype`): the relative supports of the Turán slice are
  single points with `e = (r-1)/r`; `a_τ = b_τ = 1/r`, `g_τ = (r-2)/r`, `z_τ = 0`;
  `z_η = 1/r`, `g_η = (r-1)/r`, `a_η = b_η = 0`.  Discharges `MantelNotPlantable`'s
  pinning hypothesis (`mantel_not_relatively_plantable_of_uniqueness`) and supplies the
  "consequently" clauses of §11.7 `cor:parametric-p4-turan-recovery`
  (`parametric_recovery_identities`).
* `GraphonInducedDensity` — the analytic layer of `φ_W`: the induced density
  `graphonFlagDensity W G = ∫ ∏_{i<j} wt(G.Adj i j, xᵢ, xⱼ)` of a labelled graph in a
  graphon, with relabelling invariance, the extension partition, the block product, total
  mass one, and the edge computation `= W.edgeDensity`.
* `PairSubsetCount` — the two-flag analogue of `LabeledCount`: `flagDensity₂` as a count of
  ordered pairs of vertex subsets, disjoint outside the roots, inducing the two flags
  (`flagDensity₂_eq_subset_count_div`).
* `EmptyTypeGraphBridge` — unlabelled flags as plain graphs: `graphFlag_eq_iff`,
  `graphFlag_out`, the embedding/permutation toolkit (`exists_perm_comp_emb(_pair)`), and
  the `∅ₜ` density-count formulas `flagDensity₁_graphFlag` / `flagDensity₂_graphFlag`.
* `GraphonHom` — **every graphon is a positive homomorphism**: the profile
  `graphonProfileFun W F = ℙ[W-random graph on |F| samples ≅ F]` satisfies the chain rule,
  normalisation and multiplicativity, assembling to `graphonHom W : PositiveHom ∅ₜ`
  (`positiveHomFromZeroSpaceOneMulProp`), with the sanity identity
  `graphonHom_edge : φ_W(edge) = W.edgeDensity` tying the flag-algebra and kernel layers.
* `StdRootedBridge` — sub-project A, module 0 of `HOM_TO_GRAPHON_DESIGN.md`: standard-rooted
  graphs at a two-vertex type (`RootCompatible`/`mkStdRooted`), flag equality iff root-fixing
  isomorphism, standard-rooted representatives, the root-fixing permutation engine
  (`exists_rootfix_perm_comp_emb(_pair)`), and the rooted density-as-subset-count formula
  (`flagDensity₁_stdRooted`).
* `GraphonRootedDensity` — sub-project A, module 1a: the unnormalised rooted density
  `unnormRootedDensity` (induced weight with the root coordinates pinned), the root factor
  `rootWeight`/`RootAdmissible`, root-fixing relabelling invariance, the rooted extension
  partition, total mass = `rootWeight`, the glued block product
  (`unnormRootedDensity_block_mul`, sharing the root pair), and the subset↔embedding bridge
  (`exists_rootFixing_emb_range`, `stdRooted_subset_iso_iff`).
* `GraphonRootedHom` — sub-project A, module 1b: **the rooted conditional homomorphism**.
  The conditional profile `graphonRootedProfileFun` (standard-rooted class sums over
  `rootWeight`) satisfies the chain rule, normalisation and multiplicativity at every
  admissible pinned pair, assembling to `graphonRootedHom W σ' u v h : PositiveHom σ'` — the
  view of `φ_W` from a `W`-random root pair — with joint measurability in the pair
  (`measurable_graphonRootedProfileFun`) for the upcoming rooted-view measure.
* `GraphonRootedMeasure` — sub-project A, module 2a: **the rooted-view measure is the
  extension measure**.  The normalised `rootWeight`-weighted law of the rooted conditional
  homomorphism equals `ℙ[graphonHom W]` (`rootedViewMeasure_eq_extend`), via the
  rooted-vs-unrooted counting bridge (`card_stdRooted_class`, a same-size double count
  against `downwardNormalizingFactor`) and the bridge integral identity
  (`integral_rootedClassSum`).
* `GraphonKernelTransport` — sub-project A, module 2b (capstone): the kernel dictionary
  (`graphonRootedHom_a_tau/_b_tau/_g_tau/_z_eta/_g_eta`: rooted three-vertex flag values are
  `deg`/`codeg` expressions) and the transport of the `K₄`-free `P₄`-slice equations into
  the a.e. kernel hypotheses of `Graphon.r3_rigidity`
  (`k4freeP4_graphon_Rtau_eq_zero`/`_Reta_eq_zero`), assembling to
  **`k4freeP4_graphon_tripartite`**: any graphon whose `φ_W` lies in the `K₄`-free
  `P₄`-slice is a.e. the balanced complete tripartite graphon — the graphon-side content of
  `thm:k4free-p4-tripartite`, awaiting only the representation existence (sub-project B).
* `GraphonStep` — sub-project B, module 3: step graphons.  The cell map `cellIdx` (equal
  `N`-cell interval partition, fibres of volume `1/N`), the indicator kernel
  `stepGraphon hN G`, and the pointwise indicator identity `inducedWeight_stepGraphon`
  (the induced weight of `H` at samples `c` is the indicator of the literal equality
  `G.comap (cellIdx ∘ c) = H`).
* `GraphonCounting` — sub-project B, module 4 (the pre-checkpoint payoff): the counting
  lemma `graphonProfileFun_stepGraphon_sub_le` with explicit error `n(n−1)/N` (injective
  cell tuples reproduce the finite subset count; non-injective mass and the
  falling-factorial defect each contribute `C(n,2)/N`), and **density of the graphon-hom
  range**: `exists_graphonHomPoint_seq_tendsto` — every `φ : PositiveHom ∅ₜ` is a limit of
  `graphonHomPoint` points.  With `positiveHomSpace_isClosed`, the representation theorem
  `exists_graphon_rep` is now equivalent to `IsClosed (Set.range graphonHomPoint)`
  (module 5, gated behind the design spike of `HOM_TO_GRAPHON_DESIGN.md`).
* `GraphonRepresentation` — the Route-3 closure of Phase 4 (per the checkpoint-spike
  verdict): `posHomPoint_eq_of_graphonProfileFun_eq`, the **unconditional paper-verbatim
  Thm 102** `k4free_p4_tripartite_of_represents` (*every* graphon representing a point of
  the `K₄`-free `P₄`-slice is a.e. the balanced complete tripartite graphon — the paper's
  own quantifier, no representation-existence input needed), and the existence form
  `k4free_p4_tripartite_of_rep_exists` conditional on the one named classical input of
  Phase 4, `hrep` (Lovász–Szegedy existence; its retirement plan — the weak-regularity
  campaign — is costed in the design doc).
* `GraphonParametricTransport` — `cor:top-endpoint-recovery` (Cor 106) and the `R_τ⁻`
  kernel functional.  The general-`r` rooted transports
  (`parametricP4_graphon_Rtau_eq_zero`/`_Reta_eq_zero`), the hom→kernel bridge
  `graphonHom_f₂_eq_RtauMinus : φ_W(f₂) = R_τ⁻(W)` (via the extension-measure spec — no
  new density computations), the kernel-level Thm 112(i) clause
  `parametricP4_graphon_RtauMinus_le` and its exact-slice vanishing, and the top-endpoint
  recovery: slice membership + the single scalar pin `edgeDensity = α_r⁺` identify the
  graphon a.e. with the balanced complete `r`-partite graphon
  (`parametricP4_graphon_top_endpoint_rigidity`, with the paper-verbatim
  `parametricP4_top_endpoint_of_represents` and `hrep`-conditional forms).
* `ParametricStabilityModulus` — `thm:parametric-quant-stability` (iv) (Thm 112(iv)): the
  `ω_Zyk` route, with the modulus abstracted as in `stability_via_modulus` — a certificate
  deficit `Δ ≤ p₀(r)·ω` forces the `K₄` density within `ω` of extremal, triggering the
  modulus's conclusion (`parametric_stability_via_modulus`, plus the graphon-facing
  instantiation).
-/
