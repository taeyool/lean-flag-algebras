# Reading guide

How to read and navigate the MetaTheory Lean files. See [`README.md`](./README.md) for *what* is
proved and [`ARCHITECTURE.md`](./ARCHITECTURE.md) for *how the modules fit together*.

The development is 62 modules under `MetaTheory/`, aggregated in [`../MetaTheory.lean`](../MetaTheory.lean).

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
| Lemma 1 | §2 `lem:support-as` (l.444) | `MeasureSupport` | `ae_nonneg_iff_nonneg_on_support` |
| — | §3 quotient algebra / `Q_σ` | `ConstrainedClass` | `ConstrainedAlgebra`, `qmap`, `Qσ`, `mem_Qσ_iff`, `Qσ_isClosed` |
| — | §3 forbidden-ideal faithfulness | `ForbiddenIdeal` | `forbiddenIdeal_eq_span` |
| Lemma 2 | §3 `lem:support-passes-general` (l.552) | `SupportClosure` | `support_passes` |
| Definition 3 | §4 `def:root-planting` (l.579) | `SupportClosure` | `Sσ`, `RootPlantable`, `Sσ_subset_Qσ` |
| Theorem 4 | §4 `thm:support-criterion` (l.603) | `SupportClosure` | `support_criterion`, `quotient_implies_ensemble` |
| Definition 5 | §5 `def:independent-blow-up` (l.697) | `Blowup` | `independentBlowup`, `blowupProj`, `cliqueFree_independentBlowup` |
| Lemma 9 | §5 `lem:planted-mass` (l.1170) | `Blowup` | `planted_mass` |
| Lemma 8 | §5 `lem:planted-estimate` (l.756) | `PlantedEstimate` | `planted_estimate` (uniform-clone form) |
| — | — (its general TV bound) | `ProductTV` | `prod_tv_bound`, `l1_normalization_bound` *(superseded)* |
| Theorem 10 | §5 `thm:clone-root-plantable` (l.1233) | `CloneClosed` | `clone_root_plantable` |
| Corollary 11 | §5 `cor:clique-free` (l.1385) | `CloneClosed` | `clique_free_root_plantable`, `clique_free_quotient_iff_ensemble` |
| — | (new) constrained representation thm | `ConstrainedRep` | `exists_constrained_flagSeq_limit` |
| — | §6 `def:complete-blow-up` / §7 `def:substitution-closed` | `SubstitutionBlowup` | `subBlowup`, `completeBlowup` |
| Lemma 14 / Lemma 20 | §6 `lem:true-planted-estimate` (l.1444) / §7 `lem:general-planting-estimate` (l.1781) (planting is blind to the interior) | `SubstitutionEstimate` | `planted_mass_sub`, `planted_estimate_sub` |
| — | (engine) uniform within-class blow-up closure ⟹ root-plantable | `SubstitutionClosed` | `subst_root_plantable` |
| Definition 18 / Theorem 21 | §7 `def:blow-up-closed` (l.1740), `thm:blowup-root-plantable` (l.1828) (**the unified theorem**) | `BlowupClosed` | `oneBlowup`, `BlowupClosed`, `blowupClosed_root_plantable` |
| Lemma 19 / Corollary 22 | §7 `lem:blowup-iterate` (l.1752), `cor:closures-imply-blowup` (l.1913) | `BlowupClosed` (+ `TrueClone`/`Substitution`) | `BlowupClosed.toUniform`, `GraphClass.toBlowupClosed`, `TrueCloneClosed.toBlowupClosed`, `SubstitutionClosed.toBlowupClosed` |
| Theorem 15 | §6 `thm:true-clone-root-plantable` (l.1534) | `TrueClone` | `true_clone_root_plantable`, `true_clone_quotient_iff_ensemble` |
| Corollary 16 | §6 `cor:cluster-graphs` (l.1684) | `ClusterGraph` | `cluster_root_plantable`, `cluster_quotient_iff_ensemble` |
| Theorem 24 | §7 `thm:substitution-root-plantable` (l.1948) | `Substitution` | `substitution_root_plantable`, `substitution_quotient_iff_ensemble` |
| — | (new) host-parametric planted estimate | `PlantedEstimate` | `planted_estimate_host` |
| Theorem 27 | §8 `def:finite-local-planting`, `thm:finite-local-planting` (l.2060) | `FinitePlanting` | `FinitePlanting`, `finitePlanting_root_plantable` |
| Theorem 30 | §8 `def:sparse-root-repair`, `thm:sparse-repair-planting` (l.2182) | `SparseRootRepair` | `SparseRootRepair`, `sparseRootRepair_finitePlanting` (crux helper `counting_coupling_bound`) |
| Lemma 32 | §8 `lem:c5-nbhd` (l.2350) (+ the `C₅`-free class) | `C5Free` | `c5free_neighborhood_edge_card_le`, `c5FreeClass`, `C5g`, `c5_copy_of_pentagon` |
| Theorem 36 | §8 `def:c5-one-root-planting`, `lem:c5-planting-free`, `lem:c5-one-root-sparse-repair`, `thm:c5-one-root` (l.2443) | `C5OneRoot` | `oneRootPlant`, `oneRootPlant_c5free`, `c5FreeClass_sparseRootRepair_oneVertex`, `c5free_one_root_plantable` |
| Theorem 41 | §8 `def:c5-nonedge-planting`, `lem:c5-nonedge-planting-free`, `lem:c5-nonedge-sparse-repair`, `thm:c5-nonedge-root` (l.2547) | `C5TwoRootNonEdge` | `twoRootPlant`, `twoRootPlant_c5free`, `c5FreeClass_sparseRootRepair_twoNonEdge`, `c5free_two_root_nonedge_plantable` |
| Lemma 42 | §8 `lem:c5-blowup` (l.2563) | `C5Blowup` | `c5_blowup_free_iff_triangleFree` |
| Theorem 53 | §9 `thm:pinning` (l.3081) | `Pinning` | `pinning_obstruction` |
| Definition 43 | §9 `def:edge-degenerate` (l.2605), endpoint pinning | `EdgeObstruction` | `EdgeDegenerate`, `CoEdgeDegenerate`, `e`, `ρ`, `vtype`, `ae_e_eq_zero_of_pinned`, `ae_e_eq_one_of_pinned`, `edgeDegenerate_not_rootPlantable_of_witness` |
| Theorem 44 / Corollary 51 | §9 `thm:degenerate-obstruction` (l.2612), §9.2 `cor:codegenerate` (l.2992) (abstract) | `StarWitness` | `degenerate_not_rootPlantable`, `coDegenerate_not_rootPlantable`, `exists_Qσ_point_edge_eq`, `starLabeled`, `coStarLabeled` |
| Lemma 47 / Corollary 48 | §9.1 `lem:c4-edge-zero` (l.2682), `cor:c4-counterexample` (l.2714) | `C4Free` | `c4FreeClass`, `c4free_card_edges_sq_le`, `c4FreeClass_edgeDegenerate`, `c4free_not_rootPlantable`, `c4_copy_of_square` |
| Corollary 49 | §9.1 `cor:degenerate-family` (l.2721) (general criterion; see scope note below) | `DegenerateFamily` | `edgeDegenerate_of_subquadratic` |
| Corollary 51 | §9.2 `cor:codegenerate` (l.2992) (concrete dense) | `DenseObstruction` | `coC4FreeClass`, `coC4FreeClass_coEdgeDegenerate`, `coC4free_not_rootPlantable` |
| Lemma 50 | §9.2 `lem:complementation` (l.2743) (complementation invariance) | `FlagComplement`, `ComplementHom`, `ComplementClass`, `ComplementInvariance` | `Flag.compl`/`uncompl`, `flagDensity₁_compl`, `complHom`, `complHomeo`, `HeredClass.compl`, `complHomeo_image_Qσ`, `complHomeo_map_eq`, `complHomeo_image_Sσ`, `complementation_invariance`, `complementation_invariance_oneVertex` |
| Theorem 55 | §9.4 `thm:no-interior`, `subsec:boundary` (l.3133) (boundary / no-interior pinning) | `NoInterior`, `EdgeThinning`, `EdgeThinningLimit`, `NoInteriorThinning` | `EdgeDeletionClosed`, `thinMeasure`, `thinGraph`, `thinExpectDensity`, `thinExpectDensity_le_pow`, `exists_thinned_realization`, `exists_thinned_limit`, `exists_boolean_point_in_Sσ`, `no_interior_pinning` |
| Lemma 58 | §9.5 `lem:c5-few-triangles` (l.3320) | `C5FewTriangles` | `c5free_three_mul_triangle_le`, `three_mul_card_cliqueFinset_three_eq`, `flagDensity_unlabelledTriangle_eq`, `c5FreeClass_triangleDensity_zero` |
| Corollary 57 / Corollary 59 | §9.5 `cor:c5-no-pin` (l.3296), `cor:c5-edge-pinned` (l.3340) | `C5EdgeObstruction` | `c5free_triOverVtype_zero_on_Qvtype`, `c5free_edge_not_pinned`, `ae_Ftri_eq_zero_of_pinned`, `edgeType`, `F_tri`/`triangleFF` |
| Definition 60 / Lemma 61 | §9.5 `def:c5-book` (l.3362), `lem:c5-book` (l.3368) | `C5EdgeObstruction` | `bookLabeled`, `book_c5free`, `book_Ftri_density`, `exists_book_Qτ_point` |
| Theorem 62 | §9.5 `thm:c5-edge-not-root-plantable` (l.3392) | `C5EdgeObstruction` | `c5free_edge_not_rootPlantable`, `exists_Qσ_point_flag_eq` |
| — | §10 groundwork (evaluation bounds) | `DownwardAverage` | `abs_downward_eval_le_of_abs_le_on_Sσ`, `downward_eval_eq_zero_of_degenerate`, `downward_eval_eq_of_Sσ_singleton`, `downwardNormalizingFactor_le_one` |
| Proposition 64 / Corollary 65 | §10 `prop:empty-type` (l.3476), `cor:confined` (l.3500) | `EmptyTypeCollapse` | `extend_emptyType_eq_dirac`, `Sσ_emptyType_eq`, `emptyType_rootPlantable`, `heredClass_emptyType_rootPlantable`, `emptyType_quotient_iff_ensemble`, `ensemble_implies_quotient_emptyType` |
| Theorem 66 | §10 `thm:no-closed-certificate-gap` (l.3560) | `CertificateCones` | `quotCone`, `ensCone`, `Q0Within`, `MemQ0Closure`, `ensCone_subset_closure_quotCone`, `no_closed_certificate_gap` |
| Proposition 67 | §10 `prop:ideal-zero` (l.3634) | `VanishingIdeal` (+ final clause in `CertificateCones`) | `downward_eval_eq_zero_of_zero_on_Sσ`, `downward_mul_eval_eq_zero_of_zero_on_Sσ`, `pinned_witness_downward_eq_zero`, `downward_eval_congr_of_eqOn_Sσ`, `ensCone_eval_eq_quotCone_of_sos_agreement` |
| Proposition 68 | §10 `prop:single-point` (l.3668) | `BooleanPoint`, `SinglePoint` | `edgelessPoint`, `completePoint`, `Sσ_eq_singleton_of_edgeDegenerate`, `Sσ_eq_singleton_of_coEdgeDegenerate`, `edgeDegenerate_cone_collapse`, `coEdgeDegenerate_cone_collapse`, `smul_one_mem_quotCone_vtype` |
| Corollary 70 | §10 `cor:c5-edge-closed-inert` (l.3749) | `C5EdgeInert` | `c5free_edge_no_closed_certificate_gap`, `c5free_Ftri_zero_on_Sσ`, `c5free_Ftri_mul_downward_eq_zero` |

**Scope of `cor:degenerate-family` (Corollary 49).** Only the *abstract* subquadratic criterion
`edgeDegenerate_of_subquadratic` is formalised. The named instances in the paper (general `K_{s,t}`
with `s ≥ 3`, even cycles `C_{2k}`, planar graphs) are **not** formalised: each would instantiate the
criterion via a classical extremal bound (`ex(n, K_{s,t})`, `ex(n, C_{2k})`, planar edge counts) that
is outside the current Mathlib. The `C₄` case (`c4FreeClass_edgeDegenerate`, Lemma 47) is the one
instance that is carried through.

For line-numbered `paper.tex` ↦ Lean audit maps of **§8** and **§9 (§9.1–§9.5, incl.
`lem:complementation`)**, see the
**[Auditing the correspondence](./README.md#auditing-the-correspondence-to-papertex)** section of the
README — each row cites the paper number, `\label`, line, module, and Lean name. Statement-level
checking of §9 can equally be done from the §9 rows of the map above, together with `#print axioms`
on the headline theorems — so §9 is fully audited, not unverified.

**Scope / not yet formalised.** The formalised frontier is **through §10** — including all of §9
(`thm:pinning` Theorem 53, `lem:complementation` Lemma 50, the §9.4 boundary / no-interior theorem
`thm:no-interior` Theorem 55, the §9.5 `C₅`-edge obstruction `thm:c5-edge-not-root-plantable`
Theorem 62) and all of §10 (`sec:empty-type`: Proposition 64 through Corollary 70). Not yet
formalised (future work): the characterisation *conjecture* (`conj:characterisation`) — the one §9
result still open — §11 (relative ensembles, the `K₄`-free-`P₄` equality slice), and the non-`C₄`
degenerate families of Corollary 49. See the README's
**[Scope & limitations](./README.md#scope--limitations)** for the authoritative list.

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
  `c5free_edge_no_closed_certificate_gap` (§10). The README's
  **[Mechanical re-verification](./README.md#auditing-the-correspondence-to-papertex)** block runs the
  §8/§9 subset of these in one `printf | lake env lean` invocation.

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
