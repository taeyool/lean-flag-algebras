# Reading guide

How to read and navigate the MetaTheory Lean files. See [`README.md`](./README.md) for *what* is
proved and [`ARCHITECTURE.md`](./ARCHITECTURE.md) for *how the modules fit together*.

The development is 95 modules under `MetaTheory/`, aggregated in [`../MetaTheory.lean`](../MetaTheory.lean).

---

## Conventions

* **Namespace.** Everything is in `FlagAlgebras.MetaTheory`, with `open FlagAlgebras`. Most files
  also `open MeasureTheory`, `open Filter`, `open scoped Topology` as needed.
* **Naming.** Declaration names are descriptive `snake_case` (e.g. `clone_root_plantable`,
  `support_passes`, `mem_Qσ_iff`). There is **no** `_<n>_<k>_<m>_<i>` generated-name convention
  here — that convention belongs to the precomputed flag *data* under `LeanFlagAlgebras/Flags/`,
  which this development does not touch.
* **§6–§7 naming convention.** Two markers distinguish the generalised-blow-up layer from §5:
  the `subBlowup` *prefix* names the generalised **construction and its objects**
  (`subBlowup`, `subBlowupGraphFin`, `subBlowupLabeledGraph`, `subBlowupPlantedEmb`); the `_sub`
  *suffix* names a §6–§7 **lemma/theorem that is the analogue of the §5 declaration of the same
  base name** (`planted_estimate_sub` ↔ `planted_estimate`, `planted_mass_sub` ↔ `planted_mass`,
  `blowupFlagSeq_sub` ↔ `blowupFlagSeq`, `exists_blowup_limit_sub` ↔ `exists_blowup_limit`,
  `plantedIso_sub` ↔ `plantedIso`, `good_event_induces_iff_sub` ↔ `good_event_induces_iff`, …).
  So if you know the §5 name, the §6–§7 name is `…_sub`; the proof is the §5 proof over `subBlowup`.
* **Docstrings.** Every module opens with a `/-! # … -/` header stating its purpose, the
  `paper.tex` section/result it formalises, and its key results. Public declarations (and most
  important private helpers) carry `/-- … -/` doc-comments. Long files use `/-! ## … -/` section
  dividers. **Start with a module's header** to learn what it does before reading proofs.
* **`private`.** Helper lemmas internal to a module are `private`; the public API is the
  non-`private` declarations (these are what other modules and the documentation refer to).

## Notation cheat-sheet

| Notation | Meaning |
|---|---|
| `⟦x⟧` | quotient of a labelled graph / flag vector into the flag algebra `A^σ` |
| `⟦x⟧₀` | the `downward` (unlabel-to-empty-type) image |
| `∅ₜ` | the empty `FlagType` (no labelled vertices) — the "unlabelled" / graph world |
| `⟨σ⟩₀` | `flagType_asEmptyTypeAlgebra σ`, the type `σ` viewed as an unlabelled flag; `φ⟨σ⟩₀ > 0` is the non-degeneracy a random extension needs |
| `ℙ[φ₀]` | `probMeasure_extend_emptyType_positiveHom φ₀ …`, the random-extension measure of a base limit `φ₀` |
| `≃f` | `LabeledGraphIso` (labelled-graph / flag isomorphism) |
| `↪g` | `SimpleGraph.Embedding` (induced graph embedding) |
| `flagDensity₁ F G` | the density `p(F, G)` of flag `F` in flag `G` (a `ℚ`) |

## Key spaces and objects (and where they are defined)

These come from the surrounding `LeanFlagAlgebras/FlagAlgebra/` base, not from `MetaTheory`, but you
will meet them constantly:

* `FlagAlgebra σ` — the flag algebra `A^σ` (a commutative ℝ-algebra).
* `PositiveHom σ` — positive homomorphisms `A^σ → ℝ`.
* `PositiveHomSpace σ` — the **compact metric space `X_σ`** of such homomorphisms (a closed subset
  of `FlagDensitySpace σ`, which carries the product topology of `FinFlag σ → [0,1]`).
* `FinFlag σ` — finite σ-flags; `FlagSeq σ = ℕ → FinFlag σ` — flag sequences (graph limits).
* In `MetaTheory` (§2–§5): `Qσ`, `Sσ`, `RootPlantable`, `Constraint`, `GraphClass`, `constraintOf`,
  `independentBlowup`, `blowupLabeledGraph`, `cliqueFreeClass`.
* In `MetaTheory` (§6–§7): `subBlowup G W` (generalised blow-up, within-class family `W`),
  `completeBlowup` (`W = ⊤`), `subBlowupLabeledGraph`, `HeredClass` (hereditary class with no
  closure assumption), `TrueCloneClosed` / `SubstitutionClosed` (the closure predicates),
  `subst_root_plantable`, `clusterClass`.
* The §7 unification: `oneBlowup G v H` (single-vertex blow-up `G[v→H]`), `BlowupClosed` (the
  blow-up-closure property), and `blowupClosed_root_plantable` (the theorem of which clone-,
  true-clone- and substitution-closure are corollaries, via the `…toBlowupClosed` implications).
* In `MetaTheory` (§8): `FinitePlanting` / `SparseRootRepair` (the finite-planting and
  sparse-root-repair properties of a `HeredClass`), `finitePlanting_root_plantable` /
  `sparseRootRepair_finitePlanting` (the two criteria), `c5FreeClass` (the `C₅`-free class;
  `C5g := cycleGraph 5`, `Mem G := C5g.Free G`), the plantings `oneRootPlant` / `twoRootPlant`, and
  the `C₅` types `oneVertexType` / `twoNonEdgeType` (both `⊥`, on `Fin 1` / `Fin 2`).
* In `MetaTheory` (§9): `pinning_obstruction`, the abstract obstruction theorem saying that
  almost-sure pinning on all admissible ensembles plus a quotient point with a different value
  forces `¬ RootPlantable`.  Its §9–§9.2 instances: the one-root edge flag `e` / unlabelled edge
  `ρ = ⟦e⟧₀` at `vtype := (⊥ : FlagType (Fin 1))`, `EdgeDegenerate` / `CoEdgeDegenerate`,
  `degenerate_not_rootPlantable` / `coDegenerate_not_rootPlantable` (`thm:degenerate-obstruction`,
  witnessed by `starLabeled` / `coStarLabeled` respectively),
  `c4FreeClass` with `c4FreeClass_edgeDegenerate` / `c4free_not_rootPlantable` (`lem:c4-edge-zero` /
  `cor:c4-counterexample`), `edgeDegenerate_of_subquadratic` (`cor:degenerate-family`), and the dense
  `coC4FreeClass` / `coC4free_not_rootPlantable` (`cor:codegenerate`). `lem:complementation`
  (complementation invariance, `complementation_invariance`) is the four-module `FlagComplement` →
  `ComplementHom` → `ComplementClass` → `ComplementInvariance` stack: the complement on flags +
  density invariance (`flagDensity₁_compl`), the complemented homomorphism `complHom` packaged as a
  homeomorphism `complHomeo`, the `Q_σ`/`S_σ` transfer, and the invariance capstone.
* In `MetaTheory` (§9.4): `EdgeDeletionClosed` (every spanning subgraph of a member is a member), the
  edge-thinning stack — `thinMeasure` (product Bernoulli over `Sym2 (Fin N)`) and `thinGraph`, the
  expected induced density `thinExpectDensity`, the deterministic realization
  `exists_thinned_realization`, the thinned limit `exists_thinned_limit`, the `{0,1}`-valued "edgeless
  cloud" boolean point `exists_boolean_point_in_Sσ ∈ S_σ`, and the no-interior theorem
  `no_interior_pinning` (`thm:no-interior`: a σ-flag pinned to `c` on `S_σ` has `c ∈ {0,1}`).
* In `MetaTheory` (§9.5): the two-root edge type `edgeType` (`τ`, `⊤` on `Fin 2`), the common-neighbour
  triangle flag `F_tri` / `triangleFF` (`F_△`), the few-triangles bound `c5free_three_mul_triangle_le`
  (`lem:c5-few-triangles`, `3·T ≤ 2·e`), the a.s. edge-rooting pinning `ae_Ftri_eq_zero_of_pinned`, the
  `C₅`-free book graph `bookLabeled` (`book_c5free`, `book_Ftri_density = 1`), and the capstone
  `c5free_edge_not_rootPlantable` (`thm:c5-edge-not-root-plantable`: not root-plantable at the edge
  type), with the no-vtype-obstruction corollary `cor:c5-no-pin`.
* In `MetaTheory` (§10): the master evaluation bound `abs_downward_eval_le_of_abs_le_on_Sσ`
  (`|s| ≤ δ` on `S_σ` ⟹ `|φ₀ ⟦s⟧₀| ≤ δ` on `Q₀`) and the degenerate-type collapse
  `downward_eval_eq_zero_of_degenerate` (`DownwardAverage`); the empty-type Dirac collapse
  `extend_emptyType_eq_dirac` with `emptyType_rootPlantable` (`EmptyTypeCollapse`); the certificate
  cones `quotCone`/`ensCone` with the `Q₀`-seminorm closure `Q0Within`/`MemQ0Closure` and the
  closure equality `no_closed_certificate_gap` (`CertificateCones`); the vanishing-ideal facts
  (`VanishingIdeal`); the boolean limit points `edgelessPoint`/`completePoint` at `vtype`
  (`BooleanPoint`); the single-point collapse `Sσ_eq_singleton_of_edgeDegenerate` and the cone
  collapses (`SinglePoint`); and the `C₅`-edge inertness `c5free_edge_no_closed_certificate_gap`
  (`C5EdgeInert`).
* In `MetaTheory` (§11.2–§11.3): the relative support `relSσ Y σ` (= `S_σ(Y)`, over an arbitrary
  constraint set `Y ⊆ X₀`; `Sσ_eq_relSσ` recovers the absolute `Sσ` at `Y = Qσ forb0`), the
  relative soundness/criterion pair `relative_soundness` / `relative_criterion`
  (`RelativeSupport`); the closure invariance `relSσ_closure_eq` with the weak-continuity and
  support-semicontinuity ingredients (`RelativeClosure`); the complementary-slackness family
  `relative_slackness_*` with `downward_cauchy_schwarz`, the `√Δ` first-moment bounds (squared
  form), and `unique_slice_stability` (`RelativeSlackness`); and the matrix form
  `kernel_slackness_*` with `kernelCombo` and `eval_flagQuadraticForm` on top of the base
  library's `flagQuadraticForm` (`KernelSlackness`).
* In `MetaTheory` (§11.4–§11.8): the relative planted set `relQσ hc Y σ` (= `Q_σ(Y)`) with
  `RelativelyRootPlantable` and the planted criterion (`RelativePlanted`); the `Y`-seminorm
  closure `YWithin`/`MemYClosure`, the relative ensemble cone `relEnsCone`, and
  `no_relative_closed_certificate_gap` (`RelativeCertificateGap`); the penalty-form
  `relative_positivstellensatz(_closure)` (`RelativePositivstellensatz`); the equality slice
  `eqSlice forb0 h c` with the mining principle `equality_slice_vanishing`
  (`CertificateSliceVanishing`); the **certificate bridge** — the verified
  `CompleteGraphFreeP4.gap_identity` consumed on the slices `parametricP4Slice r` /
  `k4freeP4Slice`, yielding the `parametricP4_*`/`k4freeP4_*` equations (`ParametricP4Slice`;
  Tier-2 axioms — see Tips below); the Turán/Mantel slices `turanSlice r`/`mantelSlice` with
  their nonemptiness (`TuranLimit`), the Mantel witness `knnPlusW` (`MantelNotPlantable`), and
  the recovery/stability corollaries (`SliceRecovery`); the **Turán slice-identity stack** —
  Turán-graph automorphism transitivity making all `σ`-labellings one flag class (`TuranAut`),
  the Dirac collapse of the rooting/extension measures with the fixed limit `turanLimit`
  (`TuranDirac`), and the pinned identities `turan_slice_identity_{vtype,edge,nonEdge}` /
  `relative_mantel_vtype` / `mantel_not_relatively_plantable_of_uniqueness` /
  `parametric_recovery_identities` under the named Erdős–Simonovits hypothesis `hES`
  (`TuranSliceIdentities`); and the **graphon layer** — the
  `Graphon` structure on `unitInterval` with `deg`/`codeg`/`edgeDensity`/`degSq`/`triDensity`
  (`GraphonBasic`), the local errors `ellEta`/`ellTau` and square averages `Reta`/`Rtau` with
  the moment theorems (`GraphonMoments`), rigidity (`GraphonRigidity`), and quantitative
  stability (`GraphonQuantStability`).
* In `MetaTheory` (the `φ_W` construction, infrastructure — no `paper.tex` display): the induced
  flag density `graphonFlagDensity W G` (a `W`-random graph on `|G|` samples equals `G` exactly)
  with its relabelling invariance, extension partition, and block-product identity
  (`GraphonInducedDensity`); the two-flag subset-pair count `flagDensity₂_eq_subset_count_div`
  (`PairSubsetCount`); the unlabelled-flag/plain-graph bridge `graphFlag_eq_iff` and the
  subset-count specialisations `flagDensity₁_graphFlag`/`flagDensity₂_graphFlag`, plus the
  permutation toolkit `exists_perm_comp_emb(_pair)` (`EmptyTypeGraphBridge`); and the
  homomorphism itself, `graphonHom W : PositiveHom ∅ₜ` with its profile
  `graphonProfile`/`graphonProfileFun` and the sanity link
  `graphonHom_edge : φ_W(unlabelledEdgeFlag) = W.edgeDensity` (`GraphonHom`).
* In `MetaTheory` (the rooted transport; infrastructure,
  no `paper.tex` display of its own): standard-rooted graphs and the root-fixing permutation engine
  `exists_rootfix_perm_comp_emb(_pair)` (`StdRootedBridge`); the pinned-root induced density
  `unnormRootedDensity`/`rootWeight`/`RootAdmissible` with its extension partition and glued block
  product (`GraphonRootedDensity`); **`graphonRootedHom W σ' u v h : PositiveHom σ'`**, the rooted
  conditional homomorphism — `φ_W`'s view from a `W`-random root pair (`GraphonRootedHom`); the
  rooted-vs-unrooted counting bridge `card_stdRooted_class` and the measure identification
  **`rootedViewMeasure_eq_extend`** (the rooted-view measure **is** `ℙ[graphonHom W]`,
  `GraphonRootedMeasure`); and the kernel dictionary (`graphonRootedHom_a_tau`/`_b_tau`/`_g_tau`/
  `_z_eta`/`_g_eta`) transporting the `K₄`-free `P₄`-slice equations into a.e. kernel hypotheses,
  assembling to **`k4freeP4_graphon_tripartite`** — any graphon whose `φ_W` lies in the slice is
  a.e. the balanced complete tripartite graphon, the graphon-side content of
  `thm:k4free-p4-tripartite` (Thm 102) (`GraphonKernelTransport`; Tier-2 on the last three
  theorems). **representative-quantified closure** (`GraphonRepresentation`) then composes this with profile
  agreement (`posHomPoint_eq_of_graphonProfileFun_eq`) to give **`k4free_p4_tripartite_of_represents`**
  — the unconditional, paper-verbatim Thm 102, quantified over *representing* graphons — and
  `k4free_p4_tripartite_of_rep_exists`, the existence form conditional on the one named classical
  input `hrep` (Lovász–Szegedy existence).
* In `MetaTheory` (the general-`r` parametric transport and Thm 112(iv); no
  `paper.tex` display of their own beyond the results they close): **`GraphonParametricTransport`**
  — the `r`-free mirror of the rooted-transport stack, closing **Cor 106**
  (`cor:top-endpoint-recovery`). The `r`-independent kernel functional **`Graphon.RtauMinus`**
  (`= ∫∫W(x,y)(d(x)−d(y))²`, with its a.e. characterisation `RtauMinus_eq_zero_iff_ae`); the
  **`f₂` hom→kernel bridge** `graphonHom_f₂_eq_RtauMinus : φ_W(f₂) = R_τ⁻(W)` (via the
  extension-measure spec — no new density computations, the key insight reused for the kernel-level
  third clause of Thm 112(i), `parametricP4_graphon_RtauMinus_le`); the general-`r` transports
  `parametricP4_graphon_Rtau_eq_zero`/`_Reta_eq_zero` (mirroring the `r = 3` ones); the kernel-level
  Cor 106 `parametricP4_graphon_top_endpoint_rigidity` (slice membership + the scalar pin
  `edgeDensity = α_r⁺` force the balanced complete `r`-partite graphon via `Graphon.slice_rigidity`);
  and, in the representative-quantified pattern above, **`parametricP4_top_endpoint_of_represents`** /
  `_of_rep_exists`. **`ParametricStabilityModulus`** closes **Thm 112(iv)** (`ω_Zyk` route):
  `parametric_stability_via_modulus` (hom level) and `parametric_graphon_stability_via_modulus` (the
  graphon-facing instantiation) — notably, the Zykov *bound* hypothesis `hZykov` turns out **not**
  to be needed at all (the near-extremal `K₄`-density approximation drops the certificate's Zykov
  term without using its sign, so the assumed modulus `hmod` is the only classical content). Both
  modules Tier-2.

---

## Suggested reading orders

**(a) "Just show me the main theorem."**
[`README.md`](./README.md) → the capstone walkthrough in [`ARCHITECTURE.md`](./ARCHITECTURE.md) →
the headers + `clone_root_plantable` / `clique_free_root_plantable` in
[`CloneClosed.lean`](./CloneClosed.lean).

**(b) "I care about a particular paper result."** Use the table in the README (or the map below) to
jump straight to the module and Lean name; read that module's header, then the named theorem.

**(c) "Read it end-to-end."** Follow the dependency layers (bottom-up) from
[`ARCHITECTURE.md`](./ARCHITECTURE.md):
1. **§2–§4 foundations:** `MeasureSupport` → `EvalAlgebra` → `ConstrainedClass` → `SupportClosure`
   (→ `ForbiddenIdeal`, `MeasureUniqueness`). After these you understand the support-closure
   criterion `S_σ = Q_σ ⇔` (quotient ⇔ ensemble), which is the whole point.
2. **§5 blow-up + counting:** `Blowup` → `BlowupFlag` → `DensityBridge` → `LabeledCount` →
   `CloneCount` → `CloneTotal` → `PlantedCount` → `PlantedEstimate` (with `BinomialRatio`).
3. **§5 capstone machinery:** `ConstrainedRep`, `InducedContainment` → `GraphClassConstraint`,
   `RootingUniform`, `WeakConvergence`, `BlowupSequence`.
4. **The §5 capstone:** `CloneClosed`.
5. **§6–§7 generalised blow-up:** `SubstitutionBlowup` → `SubstitutionEstimate`
   (reusing the closure-free `HeredClass` base) → `SubstitutionSequence` → `SubstitutionClosed`
   → `TrueClone`, `Substitution`, `ClusterGraph`. (Each mirrors its §5 namesake; read the module
   header first to see the one-line difference.)
6. **§8 finite planting + the `C₅`-free class:** `FinitePlanting` (the §5/§7 capstone over an
   abstract planting family — read its header to see what it reuses from `CapstoneShared`/
   `WeakConvergence`) → `SparseRootRepair` (the coupling-free sampling estimate; read
   `counting_coupling_bound`) → `C5Free` (the class + `lem:c5-nbhd`) → `C5OneRoot` →
   `C5TwoRootNonEdge` → `C5Blowup`.
7. **§9 obstruction:** `Pinning`, which is the small topological contrapositive of
   root-plantability used by the later degenerate examples.
8. **§9.1/§9.2 obstruction chain:** `EdgeObstruction` → `StarWitness` → `C4Free` →
   `DegenerateFamily` → `DenseObstruction` (the edge-pinning abstract obstruction, its star/co-star
   witnesses, the `C₄`-free counterexample, the general subquadratic criterion, and the dense
   complement obstruction). Then the four-module complement stack
   `FlagComplement` → `ComplementHom` → `ComplementClass` → `ComplementInvariance`, ending at
   `complementation_invariance` (`lem:complementation`).
9. **§9.4 boundary / no-interior (the edge-thinning stack):** `NoInterior` (`EdgeDeletionClosed`) →
   `EdgeThinning` (random Bernoulli thinning; the first-/second-moment bounds and
   `exists_thinned_realization`) → `EdgeThinningLimit` (`exists_thinned_limit`) → `NoInteriorThinning`,
   ending at `no_interior_pinning` (`thm:no-interior`). McDiarmid-free (README Deviation 10).
10. **§9.5 the `C₅`-edge obstruction:** `C5FewTriangles` (`lem:c5-few-triangles`, the triangle-density
    squeeze) → `C5EdgeObstruction` (the edge type, `F_△`, the a.s. pinning, the book-graph quotient
    point), ending at `c5free_edge_not_rootPlantable` (`thm:c5-edge-not-root-plantable`).
11. **§10 the gap is invisible to density bounds:** `DownwardAverage` (the master evaluation
    bound) → `EmptyTypeCollapse` (`prop:empty-type`/`cor:confined`) → `CertificateCones`
    (`thm:no-closed-certificate-gap`) → `VanishingIdeal` (`prop:ideal-zero`) → `BooleanPoint` →
    `SinglePoint` (`prop:single-point`) → `C5EdgeInert` (`cor:c5-edge-closed-inert`).
12. **§11.2–§11.3 the relative (slice) theory:** `RelativeSupport` (the relative support
    `relSσ` = `S_σ(Y)`, soundness, the unconditional criterion) → `RelativeClosure`
    (`lem:relative-closure`: weak continuity of `Ext_σ` + support lower-semicontinuity) →
    `RelativeSlackness` (the `relative_slackness_*` workhorse, Cauchy–Schwarz, `√Δ` first
    moments, unique-slice stability) → `KernelSlackness` (the matrix form: PSD blocks in,
    `ker Q` moment equations out).
13. **§11.4–§11.8 the slice method + graphon layer:** `RelativePlanted` (the relative planted
    set `relQσ` and the planted criterion) → `RelativeCertificateGap` /
    `RelativePositivstellensatz` (the two §11.4 completeness theorems) →
    `CertificateSliceVanishing` (`eqSlice` + the mining principle) → `ParametricP4Slice`
    (the verified certificate consumed on the `P₄` slices; Tier-2 axioms) → `TuranLimit`
    (the Turán/Mantel slices are nonempty) → `MantelNotPlantable` (the slice breaks relative
    root-plantability) → `SliceRecovery` (recovery + qualitative stability). Independently,
    the graphon layer: `GraphonBasic` (graphons on `unitInterval`, the kernel calculus) →
    `GraphonMoments` (exact + approximate moment identities) → `GraphonRigidity`
    (`slice_rigidity`/`r3_rigidity`) → `GraphonQuantStability` (quantitative stability).
14. **§11.5 the Turán slice identities (the transitivity→Dirac stack):** `TuranAut`
    (Turán-graph automorphism transitivity — translation / residue-transposition lift /
    within-class swap; all `σ`-labellings of a Turán flag are one flag class) → `TuranDirac`
    (unique labellings make the finite rooting measures Dirac; Dirac-ness passes to the weak
    limit via Mathlib's `diracProba` embedding; the fixed choice `turanLimit`) →
    `TuranSliceIdentities` (single-point relative supports with the explicit rooted densities;
    the `turan_slice_identity_*` theorems under the named Erdős–Simonovits hypothesis `hES`,
    `relative_mantel_vtype`, the `hpin`-discharged
    `mantel_not_relatively_plantable_of_uniqueness`, and Cor 105's "consequently" clauses
    `parametric_recovery_identities` — the last one Tier-2).
15. **The `φ_W` construction (every graphon is a positive homomorphism; infrastructure, no
    `paper.tex` display):** `GraphonInducedDensity` (the induced density `graphonFlagDensity` —
    why: the raw analytic input, with relabelling invariance, the extension partition, and the
    block-product identity, that the chain rule and multiplicativity below are built from) →
    `PairSubsetCount` (the two-flag density as a subset-*pair* count — why: multiplicativity is a
    joint statement about two flags, needing the pair analogue of `LabeledCount`) →
    `EmptyTypeGraphBridge` (unlabelled flags as plain graphs, plus the permutation toolkit
    `exists_perm_comp_emb(_pair)` — why: the averaging argument needs "any embedding is conjugate
    to any other by a permutation") → `GraphonHom` (assembles `graphonProfile`/`graphonHom` via
    `positiveHomFromZeroSpaceOneMulProp`, the same pattern `ComplementHom` used for `complHom`;
    ends at the sanity link `graphonHom_edge`, tying the new construction back to the §11.7
    kernel layer).
16. **The rooted transport (carries `φ_W` to the
    kernel hypotheses of `r3_rigidity`; no `paper.tex` display of its own until the capstone):**
    `StdRootedBridge` (standard-rooted graphs at a two-vertex type, flag equality iff root-fixing
    isomorphism, and the root-fixing permutation engine `exists_rootfix_perm_comp_emb(_pair)` —
    why: every root-fixing subset-averaging argument below reuses this) → `GraphonRootedDensity`
    (the pinned-root induced density `unnormRootedDensity`/`rootWeight`/`RootAdmissible`, its
    extension partition, total mass `= rootWeight`, and the glued block product — the rooted
    analogue of `GraphonInducedDensity`) → `GraphonRootedHom` (assembles
    `graphonRootedHom W σ' u v h : PositiveHom σ'`, the rooted conditional homomorphism, by
    root-fixing subset-averaging — the rooted analogue of `GraphonHom`) → `GraphonRootedMeasure`
    (the rooted-vs-unrooted counting bridge `card_stdRooted_class` and the bridge integral
    identity `integral_rootedClassSum`, assembling to **`rootedViewMeasure_eq_extend`**: the
    rooted-view measure **is** `ℙ[graphonHom W]`, via `measure_eq_of_integral_flag_eq`) →
    `GraphonKernelTransport` (the capstone: the kernel dictionary translating rooted 3-vertex flag
    values into `deg`/`codeg` expressions, transporting the `K₄`-free
    `P₄`-slice equations of `ParametricP4Slice` into the a.e. kernel hypotheses
    `k4freeP4_graphon_Rtau_eq_zero`/`_Reta_eq_zero`, and assembling to
    **`k4freeP4_graphon_tripartite`** — the graphon-side content of `thm:k4free-p4-tripartite`
    (Thm 102); Tier-2 on the last three theorems, Tier-1 upstream).
17. **Closing Thm 102, Cor 106 and Thm 112(iv) via the representative-quantified closure:**
    `GraphonRepresentation` (composes `k4freeP4_graphon_tripartite` with profile
    agreement into `k4free_p4_tripartite_of_represents`, the unconditional paper-verbatim Thm 102,
    plus the `hrep`-conditional `k4free_p4_tripartite_of_rep_exists`) → `GraphonParametricTransport`
    (the `r`-free mirror of the rooted-transport stack: the general-`r` transports,
    the `R_τ⁻` kernel functional and its `f₂` hom→kernel bridge `graphonHom_f₂_eq_RtauMinus`, and the
    same represents/rep-exists closure for **Cor 106**,
    `parametricP4_top_endpoint_of_represents`/`_of_rep_exists`) → `ParametricStabilityModulus`
    (**Thm 112(iv)**, `parametric_stability_via_modulus`, in the same modulus-abstraction
    pattern as `GraphonQuantStability.stability_via_modulus`; read its docstring for the
    hZykov-unused finding). Every §11 result in the map below is proved, modulo the
    four permanent classical inputs (README [Scope & limitations](./README.md#scope--limitations)).

**(d) "Where's the genuinely new mathematics?"** The constrained representation theorem
([`ConstrainedRep.lean`](./ConstrainedRep.lean)) and the capstone assembly
([`CloneClosed.lean`](./CloneClosed.lean), especially the private `planted_cylinder_mass`); and in
§8, the coupling-free sampling bound `counting_coupling_bound` ([`SparseRootRepair.lean`](./SparseRootRepair.lean))
and the `C₅`-freeness case analyses (`oneRootPlant_c5free`/`twoRootPlant_c5free`, and the
neighbourhood-structure `lem:c5-nbhd` in [`C5Free.lean`](./C5Free.lean)).

---

## Map: paper result → module → Lean name

The **paper number** column (`Lemma N` / `Theorem N` / etc.) is the canonical, stable identifier —
it is what an auditor reads in the PDF and what `paper.aux` assigns. The `paper.tex` line numbers
are approximate and **drift on every paper edit**; locate a result by its number or `\label{…}`,
not its line. (Lines below were last synced to the current `paper.tex`.)

| Paper # | `paper.tex` | Module | Lean declaration(s) |
|---|---|---|---|
| Lemma 1 | §2 `lem:support-as` | `MeasureSupport` | `ae_nonneg_iff_nonneg_on_support` |
| — | §3 quotient algebra / `Q_σ` | `ConstrainedClass` | `ConstrainedAlgebra`, `qmap`, `Qσ`, `mem_Qσ_iff`, `Qσ_isClosed` |
| — | §3 forbidden-ideal faithfulness | `ForbiddenIdeal` | `forbiddenIdeal_eq_span` |
| Lemma 2 | §3 `lem:support-passes-general` | `SupportClosure` | `support_passes` |
| Definition 3 | §4 `def:root-planting` | `SupportClosure` | `Sσ`, `RootPlantable`, `Sσ_subset_Qσ` |
| Theorem 4 | §4 `thm:support-criterion` | `SupportClosure` | `support_criterion`, `quotient_implies_ensemble` |
| Definition 5 | §5 `def:independent-blow-up` | `Blowup` | `independentBlowup`, `blowupProj`, `cliqueFree_independentBlowup` |
| Lemma 9 | §5 `lem:planted-mass` | `Blowup` | `planted_mass` |
| Lemma 8 | §5 `lem:planted-estimate` | `PlantedEstimate` | `planted_estimate` (uniform-clone form) |
| — | — (its general TV bound) | `ProductTV` | `prod_tv_bound`, `l1_normalization_bound` *(superseded)* |
| Theorem 10 | §5 `thm:clone-root-plantable` | `CloneClosed` | `clone_root_plantable` |
| Corollary 11 | §5 `cor:clique-free` | `CloneClosed` | `clique_free_root_plantable`, `clique_free_quotient_iff_ensemble` |
| — | (new) constrained representation thm | `ConstrainedRep` | `exists_constrained_flagSeq_limit` |
| — | §6 `def:complete-blow-up` / §7 `def:substitution-closed` | `SubstitutionBlowup` | `subBlowup`, `completeBlowup` |
| Lemma 14 / Lemma 20 | §6 `lem:true-planted-estimate` / §7 `lem:general-planting-estimate` (planting is blind to the interior) | `SubstitutionEstimate` | `planted_mass_sub`, `planted_estimate_sub` |
| — | (engine) uniform within-class blow-up closure ⟹ root-plantable | `SubstitutionClosed` | `subst_root_plantable` |
| Definition 18 / Theorem 21 | §7 `def:blow-up-closed`, `thm:blowup-root-plantable` (**the unified theorem**) | `BlowupClosed` | `oneBlowup`, `BlowupClosed`, `blowupClosed_root_plantable` |
| Lemma 19 / Corollary 22 | §7 `lem:blowup-iterate`, `cor:closures-imply-blowup` | `BlowupClosed` (+ `TrueClone`/`Substitution`) | `BlowupClosed.toUniform`, `GraphClass.toBlowupClosed`, `TrueCloneClosed.toBlowupClosed`, `SubstitutionClosed.toBlowupClosed` |
| Theorem 15 | §6 `thm:true-clone-root-plantable` | `TrueClone` | `true_clone_root_plantable`, `true_clone_quotient_iff_ensemble` |
| Corollary 16 | §6 `cor:cluster-graphs` | `ClusterGraph` | `cluster_root_plantable`, `cluster_quotient_iff_ensemble` |
| Theorem 24 | §7 `thm:substitution-root-plantable` | `Substitution` | `substitution_root_plantable`, `substitution_quotient_iff_ensemble` |
| — | (new) host-parametric planted estimate | `PlantedEstimate` | `planted_estimate_host` |
| Theorem 27 | §8 `def:finite-local-planting`, `thm:finite-local-planting` | `FinitePlanting` | `FinitePlanting`, `finitePlanting_root_plantable` |
| Theorem 30 | §8 `def:sparse-root-repair`, `thm:sparse-repair-planting` | `SparseRootRepair` | `SparseRootRepair`, `sparseRootRepair_finitePlanting` (crux helper `counting_coupling_bound`) |
| Lemma 32 | §8 `lem:c5-nbhd` (+ the `C₅`-free class) | `C5Free` | `c5free_neighborhood_edge_card_le`, `c5FreeClass`, `C5g`, `c5_copy_of_pentagon` |
| Theorem 36 | §8 `def:c5-one-root-planting`, `lem:c5-planting-free`, `lem:c5-one-root-sparse-repair`, `thm:c5-one-root` | `C5OneRoot` | `oneRootPlant`, `oneRootPlant_c5free`, `c5FreeClass_sparseRootRepair_oneVertex`, `c5free_one_root_plantable` |
| Theorem 41 | §8 `def:c5-nonedge-planting`, `lem:c5-nonedge-planting-free`, `lem:c5-nonedge-sparse-repair`, `thm:c5-nonedge-root` | `C5TwoRootNonEdge` | `twoRootPlant`, `twoRootPlant_c5free`, `c5FreeClass_sparseRootRepair_twoNonEdge`, `c5free_two_root_nonedge_plantable` |
| Lemma 42 | §8 `lem:c5-blowup` | `C5Blowup` | `c5_blowup_free_iff_triangleFree` |
| Theorem 53 | §9 `thm:pinning` | `Pinning` | `pinning_obstruction` |
| Definition 43 | §9 `def:edge-degenerate`, endpoint pinning | `EdgeObstruction` | `EdgeDegenerate`, `CoEdgeDegenerate`, `e`, `ρ`, `vtype`, `ae_e_eq_zero_of_pinned`, `ae_e_eq_one_of_pinned`, `edgeDegenerate_not_rootPlantable_of_witness` |
| Theorem 44 / Corollary 51 | §9 `thm:degenerate-obstruction`, §9.2 `cor:codegenerate` (abstract) | `StarWitness` | `degenerate_not_rootPlantable`, `coDegenerate_not_rootPlantable`, `exists_Qσ_point_edge_eq`, `starLabeled`, `coStarLabeled` |
| Lemma 47 / Corollary 48 | §9.1 `lem:c4-edge-zero`, `cor:c4-counterexample` | `C4Free` | `c4FreeClass`, `c4free_card_edges_sq_le`, `c4FreeClass_edgeDegenerate`, `c4free_not_rootPlantable`, `c4_copy_of_square` |
| Corollary 49 | §9.1 `cor:degenerate-family` (general criterion; see scope note below) | `DegenerateFamily` | `edgeDegenerate_of_subquadratic` |
| Corollary 51 | §9.2 `cor:codegenerate` (concrete dense) | `DenseObstruction` | `coC4FreeClass`, `coC4FreeClass_coEdgeDegenerate`, `coC4free_not_rootPlantable` |
| Lemma 50 | §9.2 `lem:complementation` (complementation invariance) | `FlagComplement`, `ComplementHom`, `ComplementClass`, `ComplementInvariance` | `Flag.compl`/`uncompl`, `flagDensity₁_compl`, `complHom`, `complHomeo`, `HeredClass.compl`, `complHomeo_image_Qσ`, `complHomeo_map_eq`, `complHomeo_image_Sσ`, `complementation_invariance`, `complementation_invariance_oneVertex` |
| Theorem 55 | §9.4 `thm:no-interior`, `subsec:boundary` (boundary / no-interior pinning) | `NoInterior`, `EdgeThinning`, `EdgeThinningLimit`, `NoInteriorThinning` | `EdgeDeletionClosed`, `thinMeasure`, `thinGraph`, `thinExpectDensity`, `thinExpectDensity_le_pow`, `exists_thinned_realization`, `exists_thinned_limit`, `exists_boolean_point_in_Sσ`, `no_interior_pinning` |
| Lemma 58 | §9.5 `lem:c5-few-triangles` | `C5FewTriangles` | `c5free_three_mul_triangle_le`, `three_mul_card_cliqueFinset_three_eq`, `flagDensity_unlabelledTriangle_eq`, `c5FreeClass_triangleDensity_zero` |
| Corollary 57 / Corollary 59 | §9.5 `cor:c5-no-pin`, `cor:c5-edge-pinned` | `C5EdgeObstruction` | `c5free_triOverVtype_zero_on_Qvtype`, `c5free_edge_not_pinned`, `ae_Ftri_eq_zero_of_pinned`, `edgeType`, `F_tri`/`triangleFF` |
| Definition 60 / Lemma 61 | §9.5 `def:c5-book`, `lem:c5-book` | `C5EdgeObstruction` | `bookLabeled`, `book_c5free`, `book_Ftri_density`, `exists_book_Qτ_point` |
| Theorem 62 | §9.5 `thm:c5-edge-not-root-plantable` | `C5EdgeObstruction` | `c5free_edge_not_rootPlantable`, `exists_Qσ_point_flag_eq` |
| — | §10 groundwork (evaluation bounds) | `DownwardAverage` | `abs_downward_eval_le_of_abs_le_on_Sσ`, `downward_eval_eq_zero_of_degenerate`, `downward_eval_eq_of_Sσ_singleton`, `downwardNormalizingFactor_le_one` |
| Proposition 64 / Corollary 65 | §10 `prop:empty-type`, `cor:confined` | `EmptyTypeCollapse` | `extend_emptyType_eq_dirac`, `Sσ_emptyType_eq`, `emptyType_rootPlantable`, `heredClass_emptyType_rootPlantable`, `emptyType_quotient_iff_ensemble`, `ensemble_implies_quotient_emptyType` |
| Theorem 66 | §10 `thm:no-closed-certificate-gap` | `CertificateCones` | `quotCone`, `ensCone`, `Q0Within`, `MemQ0Closure`, `ensCone_subset_closure_quotCone`, `no_closed_certificate_gap` |
| Proposition 67 | §10 `prop:ideal-zero` | `VanishingIdeal` (+ final clause in `CertificateCones`) | `downward_eval_eq_zero_of_zero_on_Sσ`, `downward_mul_eval_eq_zero_of_zero_on_Sσ`, `pinned_witness_downward_eq_zero`, `downward_eval_congr_of_eqOn_Sσ`, `ensCone_eval_eq_quotCone_of_sos_agreement` |
| Proposition 68 | §10 `prop:single-point` | `BooleanPoint`, `SinglePoint` | `edgelessPoint`, `completePoint`, `Sσ_eq_singleton_of_edgeDegenerate`, `Sσ_eq_singleton_of_coEdgeDegenerate`, `edgeDegenerate_cone_collapse`, `coEdgeDegenerate_cone_collapse`, `smul_one_mem_quotCone_vtype` |
| Corollary 70 | §10 `cor:c5-edge-closed-inert` | `C5EdgeInert` | `c5free_edge_no_closed_certificate_gap`, `c5free_Ftri_zero_on_Sσ`, `c5free_Ftri_mul_downward_eq_zero` |
| — | §11.2 the relative support `S_σ(Y)` | `RelativeSupport` | `relSσ`, `relSσ_isClosed`, `relSσ_mono`, `support_subset_relSσ`, `Sσ_eq_relSσ` |
| Lemma 71 | §11.2 `lem:relative-closure` | `RelativeClosure` | `relSσ_closure_eq`, `extend_tendsto`, `support_subset_closure_iUnion_support` |
| Proposition 72 | §11.2 `prop:relative-soundness` | `RelativeSupport` | `relative_soundness` |
| Proposition 74 | §11.2 `prop:relative-criterion` | `RelativeSupport` | `relative_criterion`, `RelEnsembleNonneg` |
| Theorem 76 (+ Remark 77 square instances) | §11.3 `thm:relative-slackness`, `rem:cs-shape` | `RelativeSlackness` | `relative_slackness_soundness`, `_approx`, `_term`, `_slack`, `_exact_slack`, `_exact_term`, `_exact_ae`, `_global`, `_exact_ae_sq`, `_global_sq` |
| Lemma 78 | §11.3 `lem:relative-cauchy-schwarz` | `RelativeSlackness` | `downward_cauchy_schwarz`, `downward_sq_eval_nonneg` |
| Corollary 79 | §11.3 `cor:sos-first-moments` | `RelativeSlackness` | `certificate_first_moment_sq_bound`, `certificate_first_moment_sq_bound_one` |
| Theorem 80 | §11.3 `thm:kernel-slackness` | `KernelSlackness` | `kernel_slackness_soundness`, `_approx`, `_exact_slack`, `_exact_ae`, `_global`; `kernelCombo`, `eval_flagQuadraticForm`, `posSemidef_dotProduct_mulVec_sq_le`, `posSemidef_mulVec_eq_zero_of_dotProduct_eq_zero` |
| Proposition 82 | §11.3 `prop:unique-slice-stability` | `RelativeSlackness` | `unique_slice_stability` |
| Definition 84 | §11.4 `def:relative-plantability` | `RelativePlanted` | `relQσ`, `RelativelyRootPlantable` |
| Proposition 85 | §11.4 `prop:relative-plantability` | `RelativePlanted` | `relQσ_isClosed`, `relQσ_subset_Qσ`, `support_subset_relQσ`, `relSσ_subset_relQσ`, `relQσ_Q0_eq`, `relativelyRootPlantable_Q0_iff`, `relQσ_nonneg_implies_relEnsemble`, `relative_planted_criterion` |
| Proposition 86 | §11.4 `prop:mantel-not-plantable` | `MantelNotPlantable`, `TuranSliceIdentities` | `mantel_not_relatively_plantable` (pinning input `hpin` = Thm 92(i), explicit hypothesis), `mantel_not_relatively_plantable_of_uniqueness` (`hpin` discharged — needs only the Erdős–Simonovits hypothesis `hES`), `exists_mantel_planted_view_edge_zero`, `knnPlusW` |
| Theorem 88 | §11.4 `thm:relative-certificate-gap` | `RelativeCertificateGap` | `no_relative_closed_certificate_gap`, `YWithin`, `MemYClosure`, `relEnsCone`, `relEnsCone_subset_closure_quotCone` |
| Theorem 89 | §11.4 `thm:relative-positivstellensatz` | `RelativePositivstellensatz` | `relative_positivstellensatz`, `relative_positivstellensatz_closure` |
| Theorem 91 *(existence + identity halves; ES as `hES`)* | §11.5 `thm:turan-slice` | `TuranLimit`, `TuranDirac`, `TuranSliceIdentities` | `turanSlice`, `turanSlice_nonempty`, `exists_turan_limit`; `turanLimit`, `turanLimit_mem_slice`; `turanLimit_relSσ_vtype`/`_edge`/`_nonEdge`, `turan_slice_identity_vtype`/`_edge`/`_nonEdge` *(identity halves (i)–(iii) under `hES`, equivalent to the paper's singleton claim; only ES itself is classical input)* |
| Theorem 92 *(existence + clause (i); ES as `hES`)* | §11.5 `thm:relative-mantel` | `TuranLimit`, `TuranSliceIdentities` | `mantelSlice`, `mantelSlice_nonempty`, `relative_mantel_vtype` *(clause (i) = `MantelNotPlantable`'s `hpin`, now a theorem under `hES`; τ/η clauses = the `r = 2` parametric instances)* |
| — | §11.5 supporting layer (the transitivity→Dirac route) | `TuranAut`, `TuranDirac` | `turan_vertex_transitive`, `turan_pair_transitive`, `labelExtensions_turan_vtype/_edge/_nonEdge_subsingleton`; `toProbMeasure_eq_dirac_of_subsingleton`, `extend_eq_dirac_of_labelExtensions_subsingleton`, `relSσ_singleton_of_extend_dirac`, `turanSubseq`/`turanLimit`/`turanLimit_spec`/`turanLimit_mem_slice` |
| Proposition 94 | §11.6 `prop:equality-slice-vanishing` | `CertificateSliceVanishing` | `equality_slice_vanishing`, `eqSlice` |
| Theorem 95 | §11.6 `thm:k4free-p4-equality-slice` | `ParametricP4Slice` | `k4freeP4_eta_equation`, `k4freeP4_tau_symm`, `k4freeP4_tau_equation`, `k4freeP4Slice`, `k4freeP4Slice_eq_parametric` *(Tier-2 axioms)* |
| Theorem 97 | §11.6 `thm:parametric-p4-equality-slice` | `ParametricP4Slice` | `parametricP4_eta_equation`, `parametricP4_tau_symm`, `parametricP4_tau_equation`, `parametricP4_K4_density` (`hZykov` hypothesis), `parametricP4Slice`, `parametricP4_cert` *(Tier-2 axioms)* |
| Theorem 99 | §11.7 `thm:parametric-moments` | `GraphonMoments` | `Graphon.moments_T`, `moments_D`, `moments_variance`, `moments_interval`, `moments_regular_iff` (kernel level, on `unitInterval` graphons) |
| Theorem 100 | §11.7 `thm:slice-rigidity` | `GraphonRigidity` | `Graphon.slice_rigidity` (measurable-partition form) |
| Corollary 101 | §11.7 `cor:r3-rigidity` | `GraphonRigidity` | `Graphon.r3_rigidity` |
| Theorem 102 *(representative-quantified form)* | §11.7 `thm:k4free-p4-tripartite` | `GraphonRepresentation` (kernel engine `Graphon.r3_rigidity`/`GraphonKernelTransport`; hom avatar still in `SliceRecovery`'s `huniq`, for Cor 104 only) | `k4free_p4_tripartite_of_represents` — unconditional, paper-verbatim, quantified over *representing* graphons (no existence input); `k4free_p4_tripartite_of_rep_exists` — the existence form conditional on the one named classical input `hrep` (Lovász–Szegedy existence) |
| Corollary 104 | §11.7 `cor:k4free-p4-qualitative-stability` | `SliceRecovery` | `k4free_qualitative_stability` (`huniq` hypothesis) |
| Corollary 105 | §11.7 `cor:parametric-p4-turan-recovery` | `SliceRecovery`, `TuranSliceIdentities` | `parametric_recovery` (`hZykEq` hypothesis), `parametric_recovery_identities` (the "consequently" support identities) *(Tier-2 axioms; Lean assumes `3 ≤ r` vs the paper's `r ≥ 4` — benign generalisation, README Deviation 15c)* |
| Corollary 106 | §11.7 `cor:top-endpoint-recovery` | `GraphonParametricTransport` (kernel engine `Graphon.slice_rigidity`) | `parametricP4_graphon_top_endpoint_rigidity` (kernel level: slice membership + the pin `edgeDensity = α_r⁺` force the balanced complete `r`-partite graphon); `parametricP4_top_endpoint_of_represents` / `_of_rep_exists` — same representative-quantified pattern as Thm 102, at general `3 ≤ r` |
| Corollary 107 | §11.7 `cor:parametric-qualitative-stability` | `SliceRecovery` | `parametric_qualitative_stability` *(Tier-2 axioms)* |
| Theorem 109 | §11.8 `thm:approximate-moments` | `GraphonMoments` | `Graphon.approximate_moments`, `approximate_moments_interval`, `approximate_moments_variance` |
| Proposition 110 | §11.8 `prop:k4free-p4-certificate-stability` | `ParametricP4Slice`, `GraphonParametricTransport` | hom level `parametricP4_sq_bounds`; the `R_τ⁻` kernel functional is now **defined** (`Graphon.RtauMinus`) with the hom→kernel bridge `graphonHom_f₂_eq_RtauMinus` and the kernel bound `parametricP4_graphon_RtauMinus_le`/`_eq_zero` *(Tier-2 axioms)* |
| Theorem 111 | §11.8 `thm:k4free-p4-quant-stability` | `GraphonQuantStability` | `Graphon.r3_edge_sq_bound`, `r3_degree_concentration`, `r3_edge_density_stability`, `r3_certificate_instance`, `stability_via_modulus` (`ω_Tur` as an abstract modulus; `δ□` not formalised) |
| Theorem 112 | §11.8 `thm:parametric-quant-stability` | `ParametricP4Slice`, `GraphonQuantStability`, `GraphonParametricTransport`, `ParametricStabilityModulus` | (i) `parametricP4_sq_bounds` + kernel clause `parametricP4_graphon_RtauMinus_le`; (ii) `parametricP4_K4_density_approx` (no Zykov input); (iii) `Graphon.interval_localisation`, `interval_localisation_below`, `quadratic_confinement`, `moment_deviation_bound`; (iv) `parametric_stability_via_modulus`/`parametric_graphon_stability_via_modulus` — the `ω_Zyk` route, also **without** needing the Zykov bound |

**Scope of `cor:degenerate-family` (Corollary 49).** Only the *abstract* subquadratic criterion
`edgeDegenerate_of_subquadratic` is formalised. The named instances in the paper (general `K_{s,t}`
with `s ≥ 3`, even cycles `C_{2k}`, planar graphs) are **not** formalised: each would instantiate the
criterion via a classical extremal bound (`ex(n, K_{s,t})`, `ex(n, C_{2k})`, planar edge counts) that
is outside the current Mathlib. The `C₄` case (`c4FreeClass_edgeDegenerate`, Lemma 47) is the one
instance that is carried through.

For line-numbered `paper.tex` ↦ Lean audit maps of **§8**, **§9 (§9.1–§9.5, incl.
`lem:complementation`)**, **§10**, **§11.2–§11.3**, and **§11.4–§11.8**, see the
**[Auditing the correspondence](./README.md#auditing-the-correspondence-to-papertex)** section of the
README — each row cites the paper number, `\label`, line, module, and Lean name. Statement-level
checking of §9 can equally be done from the §9 rows of the map above, together with `#print axioms`
on the headline theorems — so §9 is fully audited, not unverified.

**Scope.** The formalisation covers **§1–§10 in full, plus the whole of
§11 modulo four permanent classical inputs** — including all of §9 (`thm:pinning` Theorem 53,
`lem:complementation` Lemma 50, the §9.4 boundary / no-interior theorem `thm:no-interior`
Theorem 55, the §9.5 `C₅`-edge obstruction `thm:c5-edge-not-root-plantable` Theorem 62), all of §10
(`sec:empty-type`: Proposition 64 through Corollary 70), the §11.2–§11.3 relative-ensemble
foundation (Lemma 71 through Proposition 82; §11.1 is prose), all of §11.4 (Definition 84 through
Theorem 89), and every §11.5–§11.8 slice/graphon result in the map above
(classical inputs as named hypotheses — README Deviations 14–15, 18; the Thm 91/92 identity
halves and the Cor 105 "consequently" identities are formalised in the
`TuranAut`/`TuranDirac`/`TuranSliceIdentities` stack; Thm 102/Cor 106 in the represents-quantified
representative-quantified shape via `GraphonRepresentation`/`GraphonParametricTransport`; Thm 112(iv) via
`ParametricStabilityModulus`). Not formalised — by **permanent author decision**, not a gap: the
four classical results the paper itself cites as external inputs — Erdős–Simonovits stability (the
Thm 91/92 singleton claim, `hES`), Zykov's `K₄`-density bound (`hZykov`) and its equality case
(`hZykEq`), and Lovász–Szegedy existence (`hrep` — the one with a costed, optional retirement path,
the weak-regularity campaign of `HOM_TO_GRAPHON_DESIGN.md`). Remaining optional future work: the
characterisation *conjecture* (`conj:characterisation`) — the one §9 result still
open — the §12 open problems (prose), the non-`C₄` degenerate families of Corollary 49 (need
classical extremal bounds — Kővári–Sós–Turán, Bondy–Simonovits, planar — outside current
Mathlib), and a kernel-level Mantel/Turán uniqueness result that would discharge `hES`. See the
README's **[Scope & limitations](./README.md#scope--limitations)** for the authoritative list.

---

## Tips

* **Check what a theorem really depends on:** write a one-off file importing the module and
  `#print axioms <name>`, then run it (from the repo root):
  ```bash
  printf 'import LeanFlagAlgebras.MetaTheory.CloneClosed\nopen FlagAlgebras.MetaTheory\n#print axioms clone_root_plantable\n' > /tmp/chk.lean
  lake env lean /tmp/chk.lean
  ```
  A result is honest if and only if this prints only `[propext, Classical.choice, Quot.sound]` (no
  `sorryAx`). **One headline theorem per paper result** worth checking this way: `clone_root_plantable`,
  `true_clone_root_plantable`, `substitution_root_plantable`, `cluster_root_plantable`,
  `blowupClosed_root_plantable` (§5–§7 capstones); `finitePlanting_root_plantable`,
  `sparseRootRepair_finitePlanting`, `c5free_one_root_plantable`, `c5free_two_root_nonedge_plantable`
  (§8); `pinning_obstruction`, `degenerate_not_rootPlantable`, `coDegenerate_not_rootPlantable`,
  `c4free_not_rootPlantable`, `coC4free_not_rootPlantable`, `edgeDegenerate_of_subquadratic`,
  `complementation_invariance`, `no_interior_pinning`, `c5free_edge_not_rootPlantable` (§9);
  `emptyType_rootPlantable`, `heredClass_emptyType_rootPlantable`, `no_closed_certificate_gap`,
  `Sσ_eq_singleton_of_edgeDegenerate`, `edgeDegenerate_cone_collapse`,
  `c5free_edge_no_closed_certificate_gap` (§10); `relSσ_closure_eq`, `relative_soundness`,
  `relative_criterion`, `relative_slackness_global`, `downward_cauchy_schwarz`,
  `certificate_first_moment_sq_bound`, `unique_slice_stability`, `kernel_slackness_global`
  (§11.2–§11.3); `relative_planted_criterion`, `relative_positivstellensatz`,
  `no_relative_closed_certificate_gap`, `mantel_not_relatively_plantable`,
  `equality_slice_vanishing`, `exists_turan_limit`, `turan_slice_identity_vtype`,
  `mantel_not_relatively_plantable_of_uniqueness`, `Graphon.slice_rigidity`,
  `Graphon.approximate_moments` (§11.4–§11.8); `graphonHom`, `graphonHom_edge` (the `φ_W`
  construction — infrastructure, no paper result of its own, but worth the same check);
  `rootedViewMeasure_eq_extend`, `k4freeP4_graphon_tripartite` (the rooted transport — the latter
  is the graphon-side content of Thm 102, worth checking against both axiom tiers below);
  `k4free_p4_tripartite_of_represents` (`GraphonRepresentation` — the paper-verbatim Thm 102,
  representative-quantified closure); `parametricP4_top_endpoint_of_represents`
  (`GraphonParametricTransport` — the paper-verbatim Cor 106, same representative-quantified pattern) and
  `parametric_stability_via_modulus` (`ParametricStabilityModulus` — Thm 112(iv)). The
  README's
  **[Mechanical re-verification](./README.md#auditing-the-correspondence-to-papertex)** block runs the
  §8/§9 subset of these in one `printf | lake env lean` invocation.

  **Tier-2 caveat:** the §11.6–§11.7 consumers of the verified parametric certificate — the
  `parametricP4_*` / `k4freeP4_*` slice equations, `SliceRecovery`'s `parametric_recovery` /
  `parametric_qualitative_stability`, `TuranSliceIdentities`'s
  `parametric_recovery_identities` (inherited via `parametric_recovery`),
  `GraphonKernelTransport`'s `k4freeP4_graphon_Rtau_eq_zero` / `k4freeP4_graphon_Reta_eq_zero` /
  `k4freeP4_graphon_tripartite` (inherited via the `k4freeP4_*` equations they transport),
  `GraphonRepresentation`'s `k4free_p4_tripartite_of_represents` / `_of_rep_exists`, and now
  `GraphonParametricTransport`'s `parametricP4_graphon_*` / `parametricP4_top_endpoint_of_*` family
  and `ParametricStabilityModulus`'s `parametric_stability_via_modulus` /
  `parametric_graphon_stability_via_modulus` —
  legitimately print
  **two extra axioms**,
  `Lean.ofReduceBool` and `Lean.trustCompiler`, inherited from the `Automation` layer's
  `native_decide` bridges (there is no `native_decide` inside `MetaTheory`). Everything else must
  print exactly the three standard axioms. See the README's
  **[Axioms assumed](./README.md#axioms-assumed)** for the full two-tier story, including the fact
  that the `Automation` layer's declared axioms (`Zykov_K4_density_bound`,
  `Turan_limit_P4_density`) are used by **no** `MetaTheory` theorem.

* **Mechanical re-verification (the kernel-acceptance gate).** From the repo root, run
  `lake exe cache get`, then `lake build LeanFlagAlgebras.MetaTheory` (the whole layer must go green),
  then `grep -rnwE 'sorry|admit|native_decide' LeanFlagAlgebras/MetaTheory --include='*.lean'` (must
  print **nothing**). An empty grep plus a green build plus the `#print axioms` outputs above is the
  full machine-checked guarantee — every result is kernel-accepted with no escape hatches.

* **Find a definition or its uses:** `grep -rn 'planted_mass' LeanFlagAlgebras/MetaTheory` (the
  dependency table in [`ARCHITECTURE.md`](./ARCHITECTURE.md) also shows which module imports which).

* **Build one module fast** (faster than the whole tree):
  `lake build LeanFlagAlgebras.MetaTheory.PlantedEstimate`.

* **Deviations are documented in place.** Wherever the Lean differs from the paper (uniform clones,
  the constrained-representation strengthening, the `FlagDensitySpace` vs `PositiveHomSpace`
  formulation of weak convergence, the superseded `ProductTV`), the module header says so; the
  README collects them in one place.

* **Two things look like dead ends but aren't dead code:** `ForbiddenIdeal` and the top capstone
  `CloneClosed` are imported only by the aggregator — because they are *final results*, not used as
  lemmas elsewhere. The one genuinely superseded module is `ProductTV` (kept as a correct,
  reusable lemma; see README Deviation 1).
