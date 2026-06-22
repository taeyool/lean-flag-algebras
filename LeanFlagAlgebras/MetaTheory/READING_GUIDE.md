# Reading guide

How to read and navigate the MetaTheory Lean files. See [`README.md`](./README.md) for *what* is
proved and [`ARCHITECTURE.md`](./ARCHITECTURE.md) for *how the modules fit together*.

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
  forces `¬ RootPlantable`.

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

**(d) "Where's the genuinely new mathematics?"** The constrained representation theorem
([`ConstrainedRep.lean`](./ConstrainedRep.lean)) and the capstone assembly
([`CloneClosed.lean`](./CloneClosed.lean), especially the private `planted_cylinder_mass`); and in
§8, the coupling-free sampling bound `counting_coupling_bound` ([`SparseRootRepair.lean`](./SparseRootRepair.lean))
and the `C₅`-freeness case analyses (`oneRootPlant_c5free`/`twoRootPlant_c5free`, and the
neighbourhood-structure `lem:c5-nbhd` in [`C5Free.lean`](./C5Free.lean)).

---

## Map: paper result → module → Lean name

| `paper.tex` | Module | Lean declaration(s) |
|---|---|---|
| §2 `lem:support-as` (l.434) | `MeasureSupport` | `ae_nonneg_iff_nonneg_on_support` |
| §3 quotient algebra / `Q_σ` | `ConstrainedClass` | `ConstrainedAlgebra`, `qmap`, `Qσ`, `mem_Qσ_iff`, `Qσ_isClosed` |
| §3 forbidden-ideal faithfulness | `ForbiddenIdeal` | `forbiddenIdeal_eq_span` |
| §3 `lem:support-passes-general` (l.542) | `SupportClosure` | `support_passes` |
| §4 `def:root-planting` (l.569) | `SupportClosure` | `Sσ`, `RootPlantable`, `Sσ_subset_Qσ` |
| §4 `thm:support-criterion` (l.593) | `SupportClosure` | `support_criterion`, `quotient_implies_ensemble` |
| §5 `def:independent-blow-up` (l.687) | `Blowup` | `independentBlowup`, `blowupProj`, `cliqueFree_independentBlowup` |
| §5 `lem:planted-mass` (l.1160) | `Blowup` | `planted_mass` |
| §5 `lem:planted-estimate` (l.746) | `PlantedEstimate` | `planted_estimate` (uniform-clone form) |
| — (its general TV bound) | `ProductTV` | `prod_tv_bound`, `l1_normalization_bound` *(superseded)* |
| §5 `thm:clone-root-plantable` (l.1217) | `CloneClosed` | `clone_root_plantable` |
| §5 `cor:clique-free` (l.1367) | `CloneClosed` | `clique_free_root_plantable`, `clique_free_quotient_iff_ensemble` |
| (new) constrained representation thm | `ConstrainedRep` | `exists_constrained_flagSeq_limit` |
| §6 `def:complete-blow-up` / §7 `def:substitution-closed` | `SubstitutionBlowup` | `subBlowup`, `completeBlowup` |
| §6 `lem:true-planted-estimate` / §7 `lem:general-planting-estimate` (planting is blind to the interior) | `SubstitutionEstimate` | `planted_mass_sub`, `planted_estimate_sub` |
| (engine) uniform within-class blow-up closure ⟹ root-plantable | `SubstitutionClosed` | `subst_root_plantable` |
| §7 `def:blow-up-closed`, `thm:blowup-root-plantable` (**the unified theorem**) | `BlowupClosed` | `oneBlowup`, `BlowupClosed`, `blowupClosed_root_plantable` |
| §7 `lem:blowup-iterate`, `cor:closures-imply-blowup` | `BlowupClosed` (+ `TrueClone`/`Substitution`) | `BlowupClosed.toUniform`, `GraphClass.toBlowupClosed`, `TrueCloneClosed.toBlowupClosed`, `SubstitutionClosed.toBlowupClosed` |
| §6 `thm:true-clone-root-plantable` | `TrueClone` | `true_clone_root_plantable`, `true_clone_quotient_iff_ensemble` |
| §6 `cor:cluster-graphs` | `ClusterGraph` | `cluster_root_plantable`, `cluster_quotient_iff_ensemble` |
| §7 `thm:substitution-root-plantable` | `Substitution` | `substitution_root_plantable`, `substitution_quotient_iff_ensemble` |
| (new) host-parametric planted estimate | `PlantedEstimate` | `planted_estimate_host` |
| §8 `def:finite-local-planting`, `thm:finite-local-planting` | `FinitePlanting` | `FinitePlanting`, `finitePlanting_root_plantable` |
| §8 `def:sparse-root-repair`, `thm:sparse-repair-planting` | `SparseRootRepair` | `SparseRootRepair`, `sparseRootRepair_finitePlanting` (crux helper `counting_coupling_bound`) |
| §8 `lem:c5-nbhd` (+ the `C₅`-free class) | `C5Free` | `c5free_neighborhood_edge_card_le`, `c5FreeClass`, `C5g`, `c5_copy_of_pentagon` |
| §8 `def:c5-one-root-planting`, `lem:c5-planting-free`, `lem:c5-one-root-sparse-repair`, `thm:c5-one-root` | `C5OneRoot` | `oneRootPlant`, `oneRootPlant_c5free`, `c5FreeClass_sparseRootRepair_oneVertex`, `c5free_one_root_plantable` |
| §8 `def:c5-nonedge-planting`, `lem:c5-nonedge-planting-free`, `lem:c5-nonedge-sparse-repair`, `thm:c5-nonedge-root` | `C5TwoRootNonEdge` | `twoRootPlant`, `twoRootPlant_c5free`, `c5FreeClass_sparseRootRepair_twoNonEdge`, `c5free_two_root_nonedge_plantable` |
| §8 `lem:c5-blowup` | `C5Blowup` | `c5_blowup_free_iff_triangleFree` |
| §9 `thm:pinning` | `Pinning` | `pinning_obstruction` |

For a line-numbered `paper.tex` ↦ Lean audit map of §8 (what to read and what to verify), see the
**[Auditing the correspondence](./README.md#auditing-the-correspondence-to-papertex)** section of the
README.

---

## Tips

* **Check what a theorem really depends on:** write a one-off file importing the module and
  `#print axioms <name>`, then run it (from the repo root):
  ```bash
  printf 'import LeanFlagAlgebras.MetaTheory.CloneClosed\nopen FlagAlgebras.MetaTheory\n#print axioms clone_root_plantable\n' > /tmp/chk.lean
  lake env lean /tmp/chk.lean
  ```
  A result is honest iff this prints only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

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
