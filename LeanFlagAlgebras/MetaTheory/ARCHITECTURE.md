# Architecture of the MetaTheory formalisation

This document describes how the 95 Lean modules fit together: the proof strategy, the dependency
layers, a module-by-module map, and a walkthrough of the capstone proof. See
[`README.md`](./README.md) for the results and verification status, and
[`READING_GUIDE.md`](./READING_GUIDE.md) for conventions and a reading order. The precise
*Lean-name → file:line* lookup tables (paper label ↦ Lean statement ↦ `file:line`) live in
[`README.md`](./README.md) ("Auditing the correspondence to `paper.tex`") and
[`READING_GUIDE.md`](./READING_GUIDE.md); this document is the big-picture companion.

All modules live in namespace `FlagAlgebras.MetaTheory` and are aggregated by
[`../MetaTheory.lean`](../MetaTheory.lean).

---

## How to audit & re-verify

Two complementary checks establish that this directory faithfully formalises `paper.tex`.

**Statement-level audit (what to read).** Every proof here is machine-checked and `sorry`-free, so
the Lean kernel already guarantees that each result *follows from its hypotheses*. A human audit
therefore reduces to a **statement-level** comparison: read each Lean `theorem`/`def` *signature* and
check that it faithfully encodes the paper claim it says it formalises (matching hypotheses and
conclusion) — you do **not** need to read the proofs to trust them. The precise *`paper.tex`-label ↦
Lean-statement ↦ `file:line`* lookup tables that make this mechanical live in
[`README.md`](./README.md) ("Auditing the correspondence to `paper.tex`") and
[`READING_GUIDE.md`](./READING_GUIDE.md); every module also opens with a `/-! # … -/` header naming
the `paper.tex` result(s) it formalises.

**Mechanical re-verification (how to re-check by machine).** From the repository root:

```bash
lake exe cache get                                                                  # fetch Mathlib cache (don't compile from source)
lake build LeanFlagAlgebras.MetaTheory                                              # the kernel-acceptance gate (builds all 95 modules)
grep -rnwE 'sorry|admit|native_decide' LeanFlagAlgebras/MetaTheory --include='*.lean'   # → empty
```

Then confirm each headline result rests only on the standard axioms — `#print axioms <headline>`
should report `[propext, Classical.choice, Quot.sound]` and **no `sorryAx`** (e.g.
`clone_root_plantable`, `finitePlanting_root_plantable`, `pinning_obstruction`,
`complementation_invariance`, `no_interior_pinning`, `c5free_edge_not_rootPlantable`). The one
sanctioned exception: the §11.6–§11.7 consumers of the verified `CompleteGraphFreeP4.gap_identity`
certificate (the `parametricP4_*`/`k4freeP4_*` slice equations, `parametric_recovery`,
`parametric_qualitative_stability`, `parametric_recovery_identities`) additionally print `Lean.ofReduceBool` and
`Lean.trustCompiler`, inherited from the `Automation` layer's `native_decide` bridges — see the
README's "Axioms assumed" two-tier section. See the verification section of
[`README.md`](./README.md) for the full ready-to-run command block.

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

**§6–§7** keep the same argument but change the blow-up. The independent blow-up of §5 replaces each
vertex by an *edgeless* clone class; §6's complete blow-up replaces it by a *clique* and §7's
substitution by an *arbitrary in-class* graph. All three are instances of one **generalised blow-up**
`subBlowup G W` (a within-class family `W`). The crucial observation is that **off the diagonal**
(distinct base vertices) the adjacency of `subBlowup` is the base adjacency `G`, identical for all
three; and the planted estimate only ever evaluates densities on **transversals** (vertex sets
meeting each clone class at most once, where the within-class edges are never seen). So `subBlowup`
agrees with the independent blow-up on exactly the sets the §5 estimate inspects, and the whole §5
pipeline carries over. The capstone `subst_root_plantable` is `clone_root_plantable` re-run over
`subBlowup`, parameterised by an abstract *within-class blow-up closure* hypothesis; §6 supplies it
with `W = ⊤` (cliques) and §7 with in-class fibres.

**§8** takes the abstraction one step further. Instead of *any* particular construction, it isolates
the **finite planting property** (`FinitePlanting`): the only thing the capstone ever used about the
blow-up was that, from a large in-class flag `(G,θ)`, it produced a larger in-class graph `H` with a
positive-density set `Θ` of `σ`-embeddings whose bounded-size flag densities matched `(G,θ)`. Take
*that* as a hypothesis and the same six-step argument (representation → a sequence `Hₜ` → base limit
`φ₀ ∈ Q₀` with `φ₀⟨σ⟩₀ > 0` → weak convergence → Portmanteau → support) proves root-plantability —
`finitePlanting_root_plantable` (`thm:finite-local-planting`). The blow-up sequence of one fixed base
is replaced by a sequence `Hₜ` with one planting per representation term, and the cylinder-mass crux
becomes *immediate*: `|Θₜ| ≥ δ|V(Hₜ)|^k` is turned into `Pₜ(C̃) ≥ δ` by the same
`toProbMeasure_apply_eq_labeling_ratio` count identity, with no planted-estimate/`ρ` analysis. The
payoff is that a class with **no** global blow-up closure can still qualify: the `C₅`-free class
(dense, not blow-up-closed) is shown to have `FinitePlanting` at the one-vertex and two-root non-edge
types by a *sparse local repair* — clone only the roots, then delete the few old neighbourhood edges
(linear in `n` by `lem:c5-nbhd`) that a naive clone would turn into `C₅`s. The bridge
`sparseRootRepair_finitePlanting` (`thm:sparse-repair-planting`) is a finite, coupling-free sampling
estimate (a uniformly random bounded sample is unlikely to meet a root-cluster or span a repaired
edge), reusing nothing measure-theoretic.

**§9** is the negative side. The abstract engine `pinning_obstruction` uses no new graph theory: it
packages the support-closure criterion's contrapositive. If an evaluation is almost surely pinned to
a constant on every admissible random extension, closedness of the level set puts all of `S_σ` in
that level set; a quotient point outside it witnesses `S_σ ≠ Q_σ`. **§9.1–§9.2** instantiate this at
the one-vertex type with the one-root edge flag `e`: the paper's "Endpoints are automatic" remark
says a `[0,1]`-valued density of mean `0` (resp. `1`) is a.s. `0` (resp. `1`), so the degeneracy
obstruction (`thm:degenerate-obstruction`, edge density pinned to `0`, witnessed by a star) and its
dense dual (`cor:codegenerate`, pinned to `1`, witnessed by a co-star) are both *endpoint* cases of
`pinning_obstruction` reached from a mere expectation condition. The `C₄`-free class is the explicit
sparse example (edge density → 0 by the elementary Kővári–Sós–Turán bound), and its dense complement
is the explicit dense one — so density is not the dividing line. That dense example is obtained
*directly* (using complementation only at the elementary edge-count level); separately,
`lem:complementation` itself — root-plantability invariance under complementation — is formalised via
the complement *homeomorphism* of homomorphism spaces (the four-module stack described below), not the
paper's flag-algebra complement isomorphism.

**§9.4** sharpens the obstruction story for **edge-deletion-closed** classes (every spanning subgraph
of a member is a member): `thm:no-interior` says a `σ`-flag can only be pinned to `0` or `1` on `S_σ`,
never to an interior value. The argument is the **edge-thinning stack**. Keep each edge of an in-class
graph independently with probability `λ` (a product Bernoulli measure on `Sym2 (Fin N)`, `thinMeasure`);
edge-deletion closure keeps the thinned graph in the class. A first-moment bound controls the expected
induced density of any flag `M` (the *correct* induced-density form `≤ C(C(|M|,2),e(M))·λ^{e(M)}`, the
λ-independent binomial constant being harmless), and a second-moment/Chebyshev concentration —
resting on a **block-independence** lemma (two `k`-subsets sharing `≤ 1` vertex have independent
indicators, by `Measure.pi`) in place of the paper's McDiarmid inequality — produces a *deterministic*
in-class thinned realization (`exists_thinned_realization`). Diagonalising over `λ` gives a thinned
constrained limit `φ₀^λ ∈ Q₀` with positive `σ`-density (`exists_thinned_limit`, a mirror of
`FinitePlanting`'s base limit). As `λ → 0` the flag moments converge to the `{0,1}`-valued "edgeless
cloud" profile, which an L¹/Markov cylinder argument places in `S_σ` (`exists_boolean_point_in_Sσ`);
a `σ`-flag pinned to `c` on `S_σ` must then agree with that boolean point, forcing `c ∈ {0,1}`
(`no_interior_pinning`).

**§9.5** is the first **positive answer that the all-types conjecture fails**: the `C₅`-free class is
root-plantable at the one-vertex and two-root non-edge types (§8) but **not** at the two-root **edge**
type `τ` (`thm:c5-edge-not-root-plantable`). The pinned quantity is the common-neighbour triangle flag
`F_△` over `edgeType`: in a `C₅`-free graph triangles are scarce — `lem:c5-few-triangles`
(`3·T(G) ≤ 2·e(G)`, from the double-count `3·T(G) = ∑_v e(G[N(v)])` and §8's `lem:c5-nbhd`) forces the
triangle density to `0`, so `F_△` is a.s. pinned to `0` under random edge-rooting (`cor:c5-edge-pinned`,
the same squeeze pattern as §9.1's edge case). Yet the `C₅`-free **book graph** (`def:c5-book`) has
`F_△`-density `1`, giving a `Q_τ` quotient point at the opposite value, so `pinning_obstruction`
applies. The vertex type is genuinely different (`cor:c5-no-pin`): there the triangle-over-vtype
density is `0` on `Q_vtype` and the edge is not pinned, so the obstruction is *edge-type*-specific.

**§10** is the payoff that the whole obstruction half is *harmless for applications*: a flag-algebra
application outputs an empty-type density bound, and the gap is invisible there. Everything runs
through one estimate, the **master evaluation bound** (`abs_downward_eval_le_of_abs_le_on_Sσ`): if
`|s| ≤ δ` pointwise on `S_σ` then `|φ₀ ⟦s⟧₀| ≤ δ` for every `φ₀ ∈ Q₀` — for admissible `φ₀` because
`eq:extension-expectation` writes `φ₀ ⟦s⟧₀` as `φ₀ ⟦1⟧₀ ∈ [0,1]` times an integral over the support
(⊆ `S_σ`), and for degenerate `φ₀` because a degenerate base point kills *every* unlabelled average
(`downward_eval_eq_zero_of_degenerate`, proved by unlabelling the level-`ℓ` expansion of `1`).
`prop:empty-type` is a Dirac collapse: at `∅ₜ` the unlabelling operator is the identity, so `ℙ[φ₀]`
and `δ_{φ₀}` integrate every flag evaluation identically and the moment-uniqueness theorem
(`measure_eq_of_integral_flag_eq`) forces `Ext_∅(φ₀) = δ_{φ₀}`; hence `S_∅ = Q₀` and the empty type
is always root-plantable. `thm:no-closed-certificate-gap` approximates `√(max(s,0))` uniformly by a
flag evaluation (Stone–Weierstrass, `exists_flag_near`), squares it, and feeds `s − q₀²` to the
master bound with `δ = ε`; `prop:ideal-zero` is the `δ = 0` case. `prop:single-point` pins the whole
of `S_vtype` of an (co-)edge-degenerate class to the labelled empty-graph (complete-graph) limit —
the two-vertex edge (non-edge) flag dies at every constrained limit, its level-`m` expansion kills
every edge-containing (non-complete) flag, and per size exactly one flag survives the sum-to-one —
so both certificate cones collapse to the ray `ℝ≥0·1₀`. `cor:c5-edge-closed-inert` instantiates the
closed-cone equality at `(c5FreeClass, edgeType)`.

**§11.2–§11.3** relativise the whole semantic apparatus to an *arbitrary* constraint set `Y ⊆ X₀`
of admissible unlabelled limits — the foundation of the paper's slice method. The relative support
`relSσ Y σ` (= `S_σ(Y)`) generalises `Sσ` by replacing "`posHomPoint φ₀ ∈ Qσ forb0`" with
"`posHomPoint φ₀ ∈ Y`" in the same closure-of-supports definition (so `Sσ_eq_relSσ` is `rfl`), and
the two §4 "easy directions" become the *unconditional* relative criterion
(`relative_criterion` — no Urysohn, no root-plantability: relative semantics has no external
benchmark to miss). `lem:relative-closure` (`relSσ_closure_eq`) needs the only genuinely new
analysis of the layer: the random-extension map `φ ↦ ℙ[φ]` is weakly continuous where the type
density is positive (`extend_tendsto` — on flag evaluations the integral is the ratio
`φ ⟦f⟧₀ / φ ⟦1⟧₀` by the extension spec, and Stone–Weierstrass upgrades to all of `C(X_σ)` by an
ε/3 argument), and supports are lower-semicontinuous along weak convergence
(`support_subset_closure_iUnion_support`, portmanteau on open balls). On top of soundness sits the
complementary-slackness workhorse (`relative_slackness_*`): soundness drops non-negative terms;
near-equality bounds every term by the slack `Δ`; on the equality slice every term vanishes —
pointwise, almost surely under every admissible rooting (`integral_eq_zero_iff_of_nonneg_ae` at the
extension measure), and — by closure — identically on `S_σ(Y)`. Cauchy–Schwarz
(`downward_cauchy_schwarz`, the base library's extension-measure proof re-exposed) converts the
`O(Δ)` control on averaged squares into `O(√Δ)` control on first moments (kept in squared form),
and compactness alone upgrades a singleton slice to qualitative stability
(`unique_slice_stability`). The kernel form (`kernel_slackness_*`) consumes an SDP certificate's
PSD blocks directly through the base library's `flagQuadraticForm`: the pointwise PSD
Cauchy–Schwarz (`posSemidef_dotProduct_mulVec_sq_le`, proved by the quadratic discriminant) turns
each weight vector `w` into the labelled equation `wᵀQv = 0` on the slice, i.e. the moment vector
falls into `ker Q` (`posSemidef_mulVec_eq_zero_of_dotProduct_eq_zero`).

**§11.4–§11.8 is the slice method assembled from those parts.** §11.4's completeness theory
introduces the **relative planted set** `Q_σ(Y)` (`relQσ`): the density limits of in-class σ-flags
whose unlabelled flags converge into `closure Y`. Its structure theorem
(`prop:relative-plantability`) runs on rooting-measure **weak convergence + portmanteau**: the
finite rooting distributions of a planted sequence converge weakly to the extension measure, so
every support point of every admissible extension is itself a planted view
(`support_subset_relQσ`, hence `S_σ(Y) ⊆ Q_σ(Y)`), and a diagonal argument closes `Q_σ(Y)`. The
Mantel slice then *breaks* relative root-plantability (`mantel_not_relatively_plantable`): rooting
`K_{n+1,n+1}` at an adjoined isolated vertex produces a planted view with rooted edge density `0`,
while the relative support pins it to `1/2` (the pinning input is Thm 92(i), an explicit
hypothesis `hpin`). The **relative Positivstellensatz** (`relative_positivstellensatz`) is proved
**by compactness**: if no finite penalty `M·∑ g²` works for some `ε`, the sublevel sets
`K_n = {φ₀ : φ₀(g_{j_i})² ≤ 1/(n+1)}` have the finite-intersection property inside the compact
`Q₀`, and a point of the intersection lies on the slice yet violates the bound; the slice
closed-gap theorem (`no_relative_closed_certificate_gap`) re-runs §10's Stone–Weierstrass argument
over `relSσ` and the `Y`-seminorm. §11.5–§11.6 feed a **concrete verified certificate** into the
§11.3 machinery: the `Automation` layer's parametric identity `CompleteGraphFreeP4.gap_identity`
is consumed by `relative_slackness_*` on the `P₄` equality slices — the certificate's
`p₀·f₀ + leftover` remainder folded into the slack term `n` — mining the labelled `η`/`τ`
equations (`parametricP4_*`, `k4freeP4_*`); the Turán-graph sequence witnesses slice nonemptiness
(`exists_turan_limit`); and a singleton slice upgrades to qualitative stability via
`unique_slice_stability` (`SliceRecovery`, with the classical equality cases as named hypotheses).
The **graphon layer** (§11.7–§11.8) is deliberately **standalone** — kernel measure theory on
`unitInterval` with no flag-algebra imports (Mathlib has no graphons; `GraphonBasic` builds them):
the moment identities are Fubini manipulations of `deg`/`codeg` (`GraphonMoments`), and
**rigidity** (`slice_rigidity`) is a partition argument — zero variance at the regular endpoint
pins the degree, the equality case of `c ≤ d` makes a.e. section `{0,1}`-valued with zero-set of
measure `1/r`, and the `r` colour classes are grown by the **Markov-selection trick**: a
Fubini/Markov bound on the zero-set overlap kernel shows the already-selected representatives
exclude only a null-modification-small set, leaving room for a fresh generic representative at
every stage. Quantitative stability (`GraphonQuantStability`) is then explicit algebra over the
approximate moment identities, consuming the certificate-supplied `R`-bounds as hypotheses (the
flag↔kernel dictionary is part of the unformalised Lovász–Szegedy representation — README
Deviation 14b).

**The §11.5 identity halves ride a transitivity→Dirac shortcut.** The paper reads the pinned
rooted densities of `thm:turan-slice`/`thm:relative-mantel` off the graphon `T_r`; the Lean route
(`TuranAut` → `TuranDirac` → `TuranSliceIdentities`) avoids graphons **and** second-moment
computations entirely. Turán graphs are vertex- and ordered-pair transitive (translation,
residue-transposition lift, within-class swap), so all `σ`-labellings of a Turán flag form a
single flag class — hence **every finite rooting measure is exactly Dirac**
(`toProbMeasure_eq_dirac_of_subsingleton`), and Dirac-ness passes to the weak limit because
Mathlib's `diracProba` is a closed embedding on the compact metric profile space
(`extend_eq_dirac_of_labelExtensions_subsingleton`). The relative support of the singleton
constraint set collapses to one point whose coordinates are plain **single-root extension counts**
in `turanGraph (r·m) r` — the paper's values `(r-1)/r`, `1/r`, `(r-2)/r`, `0` — and the
Erdős–Simonovits singleton claim enters as the one named hypothesis `hES`
(`turanLimit_mem_slice` makes it equivalent to the paper's "exactly one point"; README
Deviation 15). Composed downstream, this discharges `MantelNotPlantable`'s `hpin`
(`mantel_not_relatively_plantable_of_uniqueness`) and completes Cor 105's "consequently" clauses
(`parametric_recovery_identities`).

**`φ_W` rides subset-averaging, not orbit counting.** The graphon→hom half of the representation
bridge (`GraphonInducedDensity` → `PairSubsetCount` → `EmptyTypeGraphBridge` → `GraphonHom`; no
single `paper.tex` display — the paper takes "every graphon is a limit object" as folklore) needs
no automorphism/orbit-stabiliser bookkeeping at all, unlike a textbook proof that a graphon's
sampled-graph distribution is exchangeable. The profile `graphonProfileFun W F` sums the induced
density `graphonFlagDensity` (the probability that a `W`-random graph on `n` samples equals a
*fixed labelled* graph `G` exactly) over **every** labelled graph `G` in the isomorphism class `F`
— so the "labelling" is never collapsed away by counting how many labellings a class has; it is
carried along explicitly in the sum. The chain rule (`zeroSpaceProp`) and multiplicativity
(`mulProp`) are then both proved by the same **subset-averaging** move: any two embeddings
`Fin n ↪ Fin ℓ` (any two *disjoint pairs* of embeddings, for the product) differ by a permutation
of `Fin ℓ` (`exists_perm_comp_emb`/`exists_perm_comp_emb_pair`, [`EmptyTypeGraphBridge`](./EmptyTypeGraphBridge.lean)),
and permuting the ambient vertex set changes neither the induced density
(`graphonFlagDensity_comap_equiv`, via a measure-preserving change of variables) nor the flag class
(`graphFlag_comap_equiv`) of what it acts on — so summing the labelled-graph fibre over any one
embedding, or averaging it over *all* size-`n` subsets, gives the same value, and the subset count
is exactly the base library's `flagDensity₁`/`flagDensity₂` (`flagDensity₁_graphFlag`/
`flagDensity₂_graphFlag`, the unlabelled specialisations of the pre-existing
`LabeledCount.flagDensity₁_eq_subset_count_div` and the new `PairSubsetCount` pair analogue).
Contrast the transitivity→Dirac route just above: there, automorphisms of *one* graph (the Turán
graph) collapse a *measure* to a Dirac mass; here, permutation-invariance of a density/class *pair*
collapses an *average* over embeddings directly, with no measure and no orbit-stabiliser count in
sight. The sanity link `graphonHom_edge : φ_W(unlabelledEdgeFlag) = W.edgeDensity` closes the loop
back to the pre-existing kernel layer (`GraphonBasic`).

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

The **§6–§7 layer** sits on top of §5, reusing it heavily (it depends on `CapstoneShared`,
`BlowupSequence`, `WeakConvergence`, `BinomialRatio`, the host-parametric `PlantedEstimate`, and the
`HeredClass` base — but *not* on the §5 capstone `CloneClosed`):

```
  §6–§7 construction + estimate        §6–§7 capstone + results
  ─────────────────────────────        ────────────────────────
  SubstitutionBlowup                   SubstitutionClosed
   (subBlowup; good-event iso)          (subst_root_plantable —
     │        │                          mirror of clone_root_plantable)
  SubstitutionEstimate   [HeredClass]            │
   (planted_*_sub)       (§5 base, reused)       ├── TrueClone   (§6 thm)
     │      via              │                    ├── Substitution (§7 thm)
     │  planted_estimate_host│                    └── ClusterGraph (§6 cor)
     └──► SubstitutionSequence ──────────────────┘
            (blowupFlagSeq_sub, base limit φ₀)
```

The §5 file `PlantedEstimate` was generalised *in place* to a host-parametric `planted_estimate_host`
(its public `planted_estimate` is now a one-line instance, so §5 is unchanged), and the
construction-agnostic capstone helpers were factored out of `CloneClosed` into the shared
**[`CapstoneShared`](./CapstoneShared.lean)** module that both capstones import (so the §6–§7 capstone
does *not* depend on the §5 one). The combinatorial counting (`CloneCount`/`CloneTotal`/`PlantedCount`),
the measure machinery (`RootingUniform`/`WeakConvergence`/`MeasureUniqueness`), and `ConstrainedRep`
are reused **verbatim**.

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

* **[`HeredClass`](./HeredClass.lean)** — the **shared class framework** (used by §5, §6 and §7).
  `graphFlag` (a graph as an `∅ₜ`-flag); the `HeredClass` structure (`Mem` + `comap` heredity, with
  *no* closure assumption); the derived `Constraint` (`constraintOf`); and the two consumption
  lemmas `mem_of_forbiddenFree` (forbidden-free ⟹ in class, via `flagDensity_self = 1`) and
  `forbiddenFree_of_mem` (in class ⟹ forbidden-free, via the containment bridge + `comap`). These
  never use any closure operation, so they serve every constrained class once.

* **[`GraphClassConstraint`](./GraphClassConstraint.lean)** — the §5 clone-closure layer.
  `GraphClass extends HeredClass` adding `clone_closed` (closure under independent blow-ups); thin
  wrappers `constraintOf` / `mem_of_forbiddenFree` / `forbiddenFree_of_mem` over the `HeredClass`
  versions (so the §5 capstone's call sites are unchanged); and the instance `cliqueFreeClass r`.

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

* **[`CapstoneShared`](./CapstoneShared.lean)** — the **construction-agnostic capstone toolkit**,
  shared by the §5 and §6–§7 capstones (and reusable for §8+): the σ-rooting-measure-as-labelling-
  count identity (`toProbMeasure_apply_eq_labeling_ratio`), closed coordinate cylinders
  (`cyl`/`isClosed_cyl`), the finite-cylinder closure criterion
  (`mem_closure_of_forall_finset_cylinder`), the asymptotic planted-gap `rhoInf`, and the
  σ-labelling/embedding counting isos (`card_labelings_eq_card_embeddings`, `embeddingIsoCongr`,
  `transportLabeled`, …). None of it mentions any specific blow-up.

### The capstone

* **[`CloneClosed`](./CloneClosed.lean)** — `thm:clone-root-plantable` + `cor:clique-free`.
  `clone_root_plantable`, `clique_free_root_plantable`, `clique_free_quotient_iff_ensemble`. Wires
  everything above together (walkthrough below), on top of `CapstoneShared` plus the §5-specific
  `embeddingEquivBlowupEmbeddings` / `blowupFlagSeq_type_pos` / `planted_cylinder_mass`.

### §6–§7 generalised blow-up

* **[`SubstitutionBlowup`](./SubstitutionBlowup.lean)** — the **generalised blow-up** `subBlowup G W`
  (within-class family `W`), introduced in code as the §6–§7 generalisation of the §5 independent
  blow-up — *not* itself a numbered paper definition; its `W = ⊤` (clique) case `completeBlowup` is
  `def:complete-blow-up` (Definition 12, the true-twin complete blow-up). Also: the off-diagonal
  agreement `subBlowup_adj_of_fst_ne`, the planted labelled graph `subBlowupLabeledGraph`, and the
  good-event isomorphism `good_event_induces_iff_sub` (obtained by composing `BlowupFlag`'s
  `blowupGoodIso` with the identity-on-a-transversal iso `subBlowupToIndepIso`).

* **[`SubstitutionEstimate`](./SubstitutionEstimate.lean)** — §6 `lem:true-planted-estimate` / §7
  `lem:general-planting-estimate` (planting is blind to the interior). `planted_mass_sub`
  (planted-root probability `≥ (λ/2k)^k`, insensitive to `W`) and `planted_estimate_sub` (density
  gap `≤ 1 − ρ`), the latter just `PlantedEstimate.planted_estimate_host` at
  `B = subBlowupLabeledGraph`, with the good-event input `good_event_induces_iff_sub`.

* The §6–§7 classes use the closure-free **[`HeredClass`](./HeredClass.lean)** base directly (see
  the §2–§5 list above) — there is no §6/§7-specific class module. Cluster graphs are a `HeredClass`
  that is *not* a `GraphClass`, which is exactly why heredity is factored out of clone-closure.

* **[`SubstitutionSequence`](./SubstitutionSequence.lean)** — the §6–§7 base side: the uniform
  generalised `(M+1)`-blow-up flag sequence `blowupFlagSeq_sub` (parameterised by a within-class
  family `Wf`), its limit `exists_blowup_limit_sub`, and `blowup_limit_mem_Q0_sub` /
  `blowup_limit_type_pos_sub`. `plantedIso_sub` shows the planted set still induces `σ` (distinct
  base vertices ⟹ base adjacency).

* **[`SubstitutionClosed`](./SubstitutionClosed.lean)** — the generalised capstone
  `subst_root_plantable`: under a *within-class blow-up closure* hypothesis (`∀ Γ ∈ class, ∀ M,
  ∃ W, subBlowup Γ W ∈ class`), `S_σ = Q_σ`. Mirrors `clone_root_plantable` line-for-line over
  `subBlowup` (with `embeddingEquivBlowupEmbeddings_sub`, `planted_cylinder_mass_sub`), reusing the
  shared `CapstoneShared` toolkit — it does **not** import the §5 capstone `CloneClosed`.

### The unification (paper §7) and the §6–§7 results

* **[`BlowupClosed`](./BlowupClosed.lean)** — the **common generalisation** of §5–§7. The
  single-vertex blow-up `oneBlowup G v H` (`def:vertex-blowup`); the **blow-up-closure** property
  `BlowupClosed` (`def:blow-up-closed` — for every member `G`, vertex `v`, and `N`, *some* order-`N`
  interior `H` keeps `oneBlowup G v H` in the class); the iteration bridge `BlowupClosed.toUniform`
  (`lem:blowup-iterate` — blowing up vertices one at a time yields a uniform full blow-up in the
  class, the hypothesis `subst_root_plantable` consumes); and the unified theorem
  `blowupClosed_root_plantable` (`thm:blowup-root-plantable`). The bridge rests on the iso
  `oneBlowup_iso` (one-vertex blow-up = one-class sub-blow-up) and `Mem_congr` (membership is
  iso-invariant). `GraphClass.toBlowupClosed` (clone-closed ⟹ blow-up-closed, edgeless interior —
  `cor:closures-imply-blowup`(1), Corollary 22) lives here; `clone_root_plantable_blowup`
  re-derives §5 as a corollary.

* **[`TrueClone`](./TrueClone.lean)** — §6 `thm:true-clone-root-plantable`. `TrueCloneClosed`
  (complete-blow-up closure), `TrueCloneClosed.toBlowupClosed` (clique interior —
  `cor:closures-imply-blowup`(2), Corollary 22), and `true_clone_root_plantable` — now a
  **corollary** of `blowupClosed_root_plantable`.

* **[`Substitution`](./Substitution.lean)** — §7 `thm:substitution-root-plantable`.
  `SubstitutionClosed` (substitution closure), `SubstitutionClosed.toBlowupClosed` (an in-class
  interior of the right size, by infinitude — `cor:closures-imply-blowup`(3), Corollary 22), and
  `substitution_root_plantable` — a **corollary** of `blowupClosed_root_plantable`. `rem:strictness`:
  substitution-closure (∀-fibre) is strictly stronger than blow-up-closure (∃-fibre) and misses
  §5/§6.

* **[`ClusterGraph`](./ClusterGraph.lean)** — §6 `cor:cluster-graphs`. Cluster graphs as the
  `P₃`-free `HeredClass` `clusterClass`, the complete-blow-up adjacency `completeBlowup_adj_iff`,
  true-clone-closure `clusterClass_trueCloneClosed`, hence `cluster_root_plantable` — root-plantable
  although **not** clone-closed (nor substitution-closed).

### §8 finite planting and the `C₅`-free class

This layer sits on top of the §5/§7 capstone toolkit (it imports `CapstoneShared`,
`WeakConvergence`, `ConstrainedRep`, `SupportClosure`, `HeredClass`, `BlowupSequence`) but **not** any
specific blow-up construction. The abstract criteria (`FinitePlanting`, `SparseRootRepair`) are
class-generic; the `C₅`-free modules then instantiate them.

```
  §8 abstract criteria                §8 C₅-free instantiation
  ────────────────────                ────────────────────────
  FinitePlanting                      C5Free  (c5FreeClass; lem:c5-nbhd;
   (thm:finite-local-planting)         C5g; c5_copy_of_pentagon)
     │                                   │           │
  SparseRootRepair                    C5OneRoot   C5TwoRootNonEdge   C5Blowup
   (thm:sparse-repair-planting)        (oneRootPlant; (twoRootPlant;     (lem:c5-blowup)
     └──────────────┬──────────────────  thm:c5-one-   thm:c5-nonedge-
                    │                     root)         root)
       both C5*Root modules consume SparseRootRepair + C5Free
```

* **[`FinitePlanting`](./FinitePlanting.lean)** — §8 `def:finite-local-planting` (`FinitePlanting`)
  and `thm:finite-local-planting` (`finitePlanting_root_plantable`). The §5 capstone
  `clone_root_plantable` re-run with the blow-up sequence replaced by the abstract planting family
  `Hₜ`. New generic helper `flagSeqLimit_mem_Q0` (the limit of forbidden-free flags lies in `Q₀` —
  the construction-free form of `blowup_limit_mem_Q0`); the uniform `σ`-type-density lower bound
  giving `φ₀⟨σ⟩₀ > 0` is recovered from `|Θₜ| ≥ δ|V|^k` via embedding↔`subgraphCount` counting. The
  Portmanteau/support tail is the `CloneClosed` tail, with the cylinder centred at `ψ` directly.
* **[`SparseRootRepair`](./SparseRootRepair.lean)** — §8 `def:sparse-root-repair` (`SparseRootRepair`,
  host vertex type `nonRoot G ⊕ (Fin n₀ × Fin L)`) and `thm:sparse-repair-planting`
  (`sparseRootRepair_finitePlanting`). The largest §8 module. Its heart is the **coupling-free**
  `counting_coupling_bound` (paper Deviation 8a): a three-term `Finset.card` inequality bounding
  `|p_H − p_G|` by `2·P_W[S⊄U] + P_W[S⊆U∧Bad]`, with the two bad-event terms estimated by binomial
  superset counts (`Finset.powersetCard`). Bridges to the flag densities by `flagDensity₁_eq_subset_count_div`
  ([`LabeledCount`](./LabeledCount.lean)) on both sides; presents the sum-type witness on `Fin N`
  (`Fintype.equivFin`, `flagDensity₁_respect_eqv`) to feed `FinitePlanting`.
* **[`C5Free`](./C5Free.lean)** — the `C₅`-free class `c5FreeClass : HeredClass` (`C5g := cycleGraph 5`,
  `Mem G := C5g.Free G` via Mathlib `IsContained`/`Free`/`Copy`), and §8 `lem:c5-nbhd`
  (`c5free_neighborhood_edge_card_le`: `e(G[N(v)]) ≤ |N(v)|`, via "`G[N(v)]` is `P₄`-subgraph-free ⟹
  each component a star or triangle"). Public helper `c5_copy_of_pentagon` (5 vertices + 5 cyclic
  edges + 10 distinctnesses ⟹ `C5g ⊑ G`), reused by both planting-free proofs.
* **[`C5OneRoot`](./C5OneRoot.lean)** — §8 one-root case: `oneRootPlant` (`def:c5-one-root-planting`),
  `oneRootPlant_c5free` (`lem:c5-planting-free`, by case analysis on how many cycle vertices land in
  the root cluster), the sparse-repair instance `c5FreeClass_sparseRootRepair_oneVertex` (clause (iii)
  injects altered pairs into `(G.induce N(r)).edgeFinset`, then `lem:c5-nbhd`), and
  `c5free_one_root_plantable` (`thm:c5-one-root`, `S₁ = Q₁`).
* **[`C5TwoRootNonEdge`](./C5TwoRootNonEdge.lean)** — §8 two-root non-edge case: `twoRootPlant`,
  `twoRootPlant_c5free` (a slick projection argument — project every cycle vertex to `G`, clones to
  their root), `c5FreeClass_sparseRootRepair_twoNonEdge` (two neighbourhoods `N(r)`, `N(s)`), and
  `c5free_two_root_nonedge_plantable` (`thm:c5-nonedge-root`, `S_η = Q_η`).
* **[`C5Blowup`](./C5Blowup.lean)** — §8 `lem:c5-blowup` (`c5_blowup_free_iff_triangleFree`): for a
  `C₅`-free `G`, every `independentBlowup` is `C₅`-free if and only if `G` is triangle-free (a triangle lifts to
  a `C₅` in the size-2 blow-up; conversely a blow-up `C₅` projects to a closed 5-walk forcing a
  triangle or a `C₅` in `G`).

### §9 pinning obstructions

* **[`Pinning`](./Pinning.lean)** — §9 `thm:pinning` (`pinning_obstruction`). The helper
  `Sσ_subset_eval_eq_of_ae_pinned` turns almost-sure pinning under every admissible random extension
  into the closed-set inclusion `S_σ ⊆ {χ | χ(g)=c}`. Then `support_pinning_obstruction` and
  `pinning_obstruction` show that any `ψ ∈ Q_σ` with `ψ(g) ≠ c` prevents root-plantability.

The §9.1–§9.2 concrete obstructions build on `Pinning` in a short chain
`EdgeObstruction → StarWitness → C4Free → {DegenerateFamily, DenseObstruction}`:

* **[`EdgeObstruction`](./EdgeObstruction.lean)** — §9 `def:edge-degenerate`. Builds the one-vertex
  type `vtype := (⊥ : FlagType (Fin 1))`, the one-root edge flag `e : A^vtype` and unlabelled edge
  `ρ := ⟦e⟧₀`, proves the denominator collapse `one_downward_vtype` (`⟦1⟧₀ = 1`) and the specialised
  expectation `expectation_e` (`∫ χ e = φ₀ ρ`), then the two endpoint a.s.-pinning facts
  `ae_e_eq_zero_of_pinned` / `ae_e_eq_one_of_pinned` (mean `0`/`1` ⟹ a.s. `0`/`1`). `EdgeDegenerate` /
  `CoEdgeDegenerate` and the abstract obstructions
  `edgeDegenerate_not_rootPlantable_of_witness` / `coEdgeDegenerate_not_rootPlantable_of_witness`
  (over `pinning_obstruction`) close the module; `Sσ_subset_e_eq_zero_of_edgeDegenerate` records the
  structured `S_v ⊆ {χ(e)=0}` half of `thm:degenerate-obstruction`.
* **[`StarWitness`](./StarWitness.lean)** — §9 the concrete witnesses. The σ-typed forbidden-freeness
  `flagDensity_forbidden_eq_zero_of_mem` (analogue of `HeredClass.forbiddenFree_of_mem`) lets a
  convergent in-class flag sequence's limit land in `Q_vtype`; `exists_Qσ_point_edge_eq` assembles
  that limit (Razborov 3.3(a) `flagSeq_limit_mem_positiveHom` + compactness
  `increasing_flagSeq_contain_convergent_subseq`). The star / co-star are built explicitly with
  `star_edge_density = 1` / `coStar_edge_density = 0`, giving `degenerate_not_rootPlantable`
  (`thm:degenerate-obstruction`) and `coDegenerate_not_rootPlantable` (`cor:codegenerate`, abstract).
* **[`C4Free`](./C4Free.lean)** — §9.1 the `C₄`-free class `c4FreeClass` (`Mem G := (cycleGraph 4).Free G`).
  The counting heart `c4free_card_edges_sq_le` (`(2·e(G))² ≤ 2|G|³`) is a cherry double-count
  (`cherry_count_eq`, `c4free_common_neighbors_le_one`, `c4_copy_of_square`) plus Cauchy–Schwarz;
  `flagDensity_unlabelledEdge_eq` rewrites the unlabelled-edge density as `e(G)/C(N,2)`. Then
  `c4FreeClass_edgeDegenerate` (`lem:c4-edge-zero`) squeezes the squared density to `0` over the
  constrained-representation sequence, and `c4free_not_rootPlantable` (`cor:c4-counterexample`) feeds a
  star into `degenerate_not_rootPlantable`. The shared analytic helpers `edgeDensity_sq_bound` /
  `edgeDensity_bound_tendsto_zero` live here and are reused by `DenseObstruction`.
* **[`DegenerateFamily`](./DegenerateFamily.lean)** — §9.1 `cor:degenerate-family`. The general
  criterion `edgeDegenerate_of_subquadratic` (subquadratic edge bound ⟹ edge-degenerate), the common
  mechanism of the listed families: `K_{s,t}`-free graphs (Kővári–Sós–Turán), even cycles `C_{2k}`
  (Bondy–Simonovits), forests / bounded-average-degree classes, and planar graphs. `C₄` (the
  `K_{2,2}` case) is the one whose bound is proved from scratch; the other families' extremal bounds
  are outside current Mathlib, so only the abstract criterion is instantiated for them.
* **[`DenseObstruction`](./DenseObstruction.lean)** — §9.2 `cor:codegenerate`, made concrete. The
  dense `coC4FreeClass` (`Mem G := (cycleGraph 4).Free Gᶜ`), its co-edge-degeneracy
  `coC4FreeClass_coEdgeDegenerate` (edge density `1 − e(Gᶜ)/C(N,2) → 1`, via the complement edge-count
  identity `card_edgeFinset_add_compl` and the `C₄` bound on `Gᶜ`), and `coC4free_not_rootPlantable`.
  The load-bearing `downwardNormalizingFactor_edge_eq_one` (so `φ₀ ρ` is the genuine edge density) is
  proved via `isomorphismCount edgeLabeled = 2`. Complementation enters only elementarily — never the
  `lem:complementation` isomorphism (which is itself formalised separately, below).

### §9.2 complementation invariance (`lem:complementation`)

A four-module stack proves that root-plantability is invariant under graph complementation — *not*
by building the paper's flag-algebra complement isomorphism `C_σ`, but by building the complement
**homeomorphism** of homomorphism spaces directly. Chain:
`FlagComplement → ComplementHom → ComplementClass → ComplementInvariance`.

* **[`FlagComplement`](./FlagComplement.lean)** — the complement on flags. `LabeledGraph.compl` /
  `Flag.compl : Flag σ V → Flag σᶜ V` and a *clean* `uncompl` involution partner (the round-trips are
  honest `Eq`, so the `σᶜᶜ` transport never appears downstream). The combinatorial heart is
  `flagDensity₁_compl` / `flagDensity₂_compl` (`flagDensity Fᶜ Gᶜ = flagDensity F G`, via the
  subset-count formula and `induce`/`compl` commutation), plus `unlabel_compl` and
  `downwardNormalizingFactor_compl` (the unlabelling weight is complement-invariant), used in the
  measure layer.
* **[`ComplementHom`](./ComplementHom.lean)** — `complHom : PositiveHom σ → PositiveHom σᶜ`, built
  *from the density profile* via `positiveHomFromZeroSpaceOneMulProp`: the three homomorphism axioms
  (`zeroSpaceProp`/`oneProp`/`mulProp`) of the complemented profile follow from the Layer-1 density
  identities by reindexing the sums along the `compl`/`uncompl` bijection. Its symmetric inverse
  `uncomplHom`, the clean mutual-inverse laws, and the homeomorphism
  `complHomeo : PositiveHomSpace σ ≃ₜ PositiveHomSpace σᶜ` (continuity coordinatewise, since
  `(complHomeo χ).val G = χ.val G.uncompl`).
* **[`ComplementClass`](./ComplementClass.lean)** — the complement hereditary class `HeredClass.compl`
  (`K̄`, `Mem G := Mem Gᶜ`, `comap` via `complEmbedding`), the forbidden-flag correspondence
  `complClass_forbσ_iff`, and the quotient-space transfer
  `complHomeo_image_Qσ : Φ '' Q_σ(K) = Q_{σᶜ}(K̄)` (via `mem_Qσ_iff` + the forbidden bridge).
* **[`ComplementInvariance`](./ComplementInvariance.lean)** — the capstone. The base complement
  homomorphism `complBase` (carrying the `∅ₜᶜ = ∅ₜ` transport), the **measure pushforward**
  `complHomeo_map_eq : Φ_* ℙ[φ₀] = ℙ[φ̄₀]` (by `measure_eq_of_integral_flag_eq`, reducing — by
  linearity to basis vectors — to matching the expectation formula, whose numerators *and*
  denominators are individually equal via `downward_basisVector` + the Layer-1 invariance lemmas),
  the support transfer `complHomeo_image_Sσ : Φ '' S_σ(K) = S_{σᶜ}(K̄)` (homeomorphism image of a
  closure-of-supports, with the index union reindexed by the `complBase` bijection), and finally
  `complementation_invariance : RootPlantable (K.constraintOf σ) ↔ RootPlantable (K̄.constraintOf σᶜ)`
  — apply the bijection `Φ` to `S_σ(K) = Q_σ(K)`. `complementation_invariance_oneVertex` is the
  `σ = vtype` corollary (`(⊥ : FlagType (Fin 1))ᶜ = ⊥`), matching the paper's final sentence.

### §9.4 boundary / no-interior pinning (the edge-thinning stack)

A four-module stack proves `thm:no-interior` (Theorem 55, `subsec:boundary`): for an
edge-deletion-closed class, a `σ`-flag pinned to `c` on `S_σ` has `c ∈ {0,1}`. Chain:
`NoInterior → EdgeThinning → EdgeThinningLimit → NoInteriorThinning`. It reuses the §8 base-limit
toolkit (`flagSeqLimit_mem_Q0`, `CapstoneShared`, `WeakConvergence`, `SupportClosure`) but introduces
a fresh probabilistic ingredient — random edge-thinning. (Proof-route deviation: McDiarmid-free, see
README Deviation 10.)

* **[`NoInterior`](./NoInterior.lean)** — the predicate `EdgeDeletionClosed` (every spanning subgraph
  of an in-class graph is in-class) and the elementary closure consequences the stack consumes.
* **[`EdgeThinning`](./EdgeThinning.lean)** — random Bernoulli edge-thinning of a finite graph: the
  product measure `thinMeasure` (`Measure.pi` of Bernoullis over `Sym2 (Fin N)`) and the thinned graph
  `thinGraph`; the expected induced density `thinExpectDensity` with the **first-moment** upper bound
  `thinExpectDensity_le_pow` (`≤ C(C(|M|,2),e(M))·λ^{e(M)}`, the *correct* induced-density form — README
  Deviation 10b) and the `σ`-type **lower** bound `thinExpectDensity_type_ge`; and the **second-moment**
  realization `exists_thinned_realization` — a deterministic in-class spanning subgraph tracking the
  expectations within `ε` (block-independence variance bound + Chebyshev + union bound, McDiarmid-free
  — README Deviation 10a). The largest §9.4 module.
* **[`EdgeThinningLimit`](./EdgeThinningLimit.lean)** — `exists_thinned_limit`: the edge-thinned
  constrained limit `φ₀^λ ∈ Q₀` (a diagonal realization mirroring `BlowupSequence`/`FinitePlanting`),
  with `σ`-density `≥ λ^{e(σ)}·φ₀⟨σ⟩₀ > 0` and per-flag bound `≤ C·λ^{e(M)}`.
* **[`NoInteriorThinning`](./NoInteriorThinning.lean)** — the capstone. `exists_boolean_point_in_Sσ`:
  as `λ → 0` the flag moments of `ℙ[φ₀^λ]` converge to the `{0,1}`-valued "edgeless cloud" profile, so
  an L¹/Markov cylinder argument places that boolean point `ψ_σ ∈ S_σ` (README Deviation 10c); then
  `no_interior_pinning` (`thm:no-interior`): a `σ`-flag pinned to `c` on `S_σ` must agree with `ψ_σ`,
  hence `c ∈ {0,1}`.

### §9.5 the `C₅`-edge obstruction (`sec:c5-edge`)

Two modules prove that the natural "root-plantable at *every* type" conjecture **fails**: the
`C₅`-free class is root-plantable at the one-vertex and two-root non-edge types (§8) but not at the
two-root **edge** type. They reuse `Pinning`, the §8 `c5FreeClass`/`lem:c5-nbhd` (`C5Free`), and the
constrained-representation + `Q_σ`-point machinery.

* **[`C5FewTriangles`](./C5FewTriangles.lean)** — §9.5 `lem:c5-few-triangles`
  (`c5free_three_mul_triangle_le`: `3·T(G) ≤ 2·e(G)` for `C₅`-free `G`), via the new combinatorial
  double-count `three_mul_card_cliqueFinset_three_eq` (`3·T(G) = ∑_v e(G[N(v)])`, `T = #cliqueFinset 3`)
  and §8's `lem:c5-nbhd`. The unlabelled-triangle density is `flagDensity_unlabelledTriangle_eq`
  (`= T(G)/C(N,3)`); `c5FreeClass_triangleDensity_zero` squeezes it to `0` over every constrained limit
  (the mirror of `c4FreeClass_edgeDegenerate`).
* **[`C5EdgeObstruction`](./C5EdgeObstruction.lean)** — §9.5 the obstruction itself. The two-root edge
  type `edgeType` (`⊤` on `Fin 2`), the common-neighbour triangle flag `F_tri`/`triangleFF`; the a.s.
  pinning `ae_Ftri_eq_zero_of_pinned` (`cor:c5-edge-pinned`: `F_△` pinned to `0` under random
  edge-rooting); the `C₅`-free **book graph** `bookLabeled` (`def:c5-book`) with `book_c5free`
  (`lem:c5-book`) and `book_Ftri_density = 1`; the `Q_τ` point `exists_book_Qτ_point` (assembled by the
  generic `exists_Qσ_point_flag_eq`, any `σ`, any flag); and the capstone
  `c5free_edge_not_rootPlantable` (`thm:c5-edge-not-root-plantable`) — not root-plantable at the
  edge type, refuting the all-types conjecture. `cor:c5-no-pin` is the two no-obstruction-at-vtype
  facts `c5free_triOverVtype_zero_on_Qvtype` and `c5free_edge_not_pinned`.

### §10 the gap is invisible to density bounds (`sec:empty-type`)

Seven modules; the engine is the master evaluation bound, everything else is paper-ordered on top.
They reuse `SupportClosure` (`Sσ`, `support_criterion`), the random-extension spec, the
moment-uniqueness theorem `measure_eq_of_integral_flag_eq`, Stone–Weierstrass `exists_flag_near`,
the §9 `EdgeObstruction` layer, and the base-library expansion lemmas
(`basisVector_quot_eq_sum`, `sum_flagWithSize_eq_one`).

* **[`DownwardAverage`](./DownwardAverage.lean)** — the `posHomPoint`/`toPosHom` roundtrips; the
  unlabelling weight is a probability (`downwardNormalizingFactor_le_one`, by injecting label
  placements into `Fin n₀ ↪ Fin n`), so `φ₀ ⟦1⟧₀ ∈ [0,1]`; the degenerate-type collapse
  `downward_eval_eq_zero_of_degenerate`; the **master evaluation bound**
  `abs_downward_eval_le_of_abs_le_on_Sσ`; and the singleton collapse
  `downward_eval_eq_of_Sσ_singleton`.
* **[`EmptyTypeCollapse`](./EmptyTypeCollapse.lean)** — §10 `prop:empty-type` + `cor:confined`:
  `⟨∅ₜ⟩₀ = 1` (every base limit is admissible), the Dirac identity `extend_emptyType_eq_dirac`,
  `Sσ_emptyType_eq` (`S_∅ = Q₀`), `emptyType_rootPlantable` / `heredClass_emptyType_rootPlantable`,
  and the semantic coincidence `emptyType_quotient_iff_ensemble` /
  `ensemble_implies_quotient_emptyType`.
* **[`CertificateCones`](./CertificateCones.lean)** — §10 `thm:no-closed-certificate-gap`: the cones
  `quotCone` (ambient sums of squares, Mathlib `IsSumSq` — README Deviation 12b) and `ensCone`, the
  ε-form `Q₀`-closure (`Q0Within`/`MemQ0Closure` — 12a), the Stone–Weierstrass crux
  `ensCone_subset_closure_quotCone`, and `no_closed_certificate_gap` (for every type — 12d).
* **[`VanishingIdeal`](./VanishingIdeal.lean)** — §10 `prop:ideal-zero`, four `δ = 0` instances of
  the master bound (core, ideal/multiple, pinning-witness, congruence forms; evaluation form — 12c).
* **[`BooleanPoint`](./BooleanPoint.lean)** — the labelled empty-graph / complete-graph limits
  `edgelessPoint` / `completePoint` in `X_vtype`: `IsEdgelessFlag`/`IsCompleteFlag`, per-size
  uniqueness of the edgeless/complete flag (at `vtype` and `∅ₜ`), existence as rooted flag-sequence
  limits, and the profile workhorse `val_eq_boolean_of_nonEdgeless_zero` (+ `…nonComplete…`).
* **[`SinglePoint`](./SinglePoint.lean)** — §10 `prop:single-point`: the two-vertex edge/non-edge
  density positivity, the flag-killing lemmas (`eval_eq_zero_of_edgeDegenerate` /
  `…coEdgeDegenerate`), the a.s. vanishing of non-boolean flags,
  `Sσ_eq_singleton_of_edgeDegenerate` / `…coEdgeDegenerate`, and the cone collapses
  `edgeDegenerate_cone_collapse` / `coEdgeDegenerate_cone_collapse` (with
  `smul_one_mem_quotCone_vtype`); the co-case is a direct mirror (12e).
* **[`C5EdgeInert`](./C5EdgeInert.lean)** — §10 `cor:c5-edge-closed-inert`:
  `c5free_edge_no_closed_certificate_gap` (instance of Thm 66), `c5free_Ftri_zero_on_Sσ`
  (a.s. pinning upgraded to all of `S_τ`), `c5free_Ftri_mul_downward_eq_zero` (Prop 67 applied).

### §11.2–§11.3 the relative (slice) theory

Four modules; a thin, reuse-heavy layer — `RelativeSupport` mirrors `SupportClosure`/
`DownwardAverage` over an arbitrary `Y`, `RelativeClosure` is the one new analytic result, and the
two slackness modules are consequences of `relative_soundness` plus the extension-measure spec.

* **[`RelativeSupport`](./RelativeSupport.lean)** — the relative support `relSσ Y σ` (= `S_σ(Y)`;
  `Sσ_eq_relSσ` recovers `Sσ` at `Y = Qσ forb0` by `rfl`), `support_subset_relSσ`/`relSσ_mono`,
  relative soundness `relative_soundness` (`prop:relative-soundness`; the degenerate case via
  `downward_eval_eq_zero_of_degenerate`), and the **unconditional** relative criterion
  `relative_criterion` (`prop:relative-criterion`) with `RelEnsembleNonneg` — both directions are
  the "easy" directions of `thm:support-criterion`, no Urysohn function needed.
* **[`RelativeClosure`](./RelativeClosure.lean)** — `lem:relative-closure` (`relSσ_closure_eq`:
  `S_σ(closure Y) = S_σ(Y)`), from weak continuity of the random extension (`extend_tendsto`;
  flag-evaluation integrals are evaluation-continuous ratios by the extension spec, ε/3 +
  `exists_flag_near` upgrades to all bounded continuous functions) and support
  lower-semicontinuity along weak convergence (`support_subset_closure_iUnion_support`;
  portmanteau `ProbabilityMeasure.le_liminf_measure_open_of_tendsto` on open balls +
  `Measure.measure_compl_support`).
* **[`RelativeSlackness`](./RelativeSlackness.lean)** — `thm:relative-slackness` as the
  `relative_slackness_*` family (soundness / aggregate / per-term / slack-term approximate bounds;
  slack, term, and almost-sure exact vanishing; global vanishing on `S_σ(Y)` via
  `ae_nonneg_iff_nonneg_on_support` applied to `±f` and `closure_minimal`; plus the `rem:cs-shape`
  square instances `relative_slackness_exact_ae_sq` / `relative_slackness_global_sq`, reading
  `ψ(l) = 0` a.s. and `l = 0` on `S_{σᵢ}(Y)` when `fᵢ = l·l`); Cauchy–Schwarz
  `downward_cauchy_schwarz` (wrapper over the base library's
  `square_downward_mul_ge_mul_downward_square`); the `√Δ` first-moment bounds in squared form
  (`certificate_first_moment_sq_bound(_one)`); and `unique_slice_stability`
  (`tendsto_of_subseq_tendsto` + compactness of `X₀`).
* **[`KernelSlackness`](./KernelSlackness.lean)** — `thm:kernel-slackness` as the five-part
  `kernel_slackness_*` family over the base library's `flagQuadraticForm` (`⟨Qv,v⟩`): the
  evaluation identity `eval_flagQuadraticForm` (moment-vector quadratic form), two elementary
  real-PSD facts by the quadratic discriminant (`posSemidef_dotProduct_mulVec_sq_le`,
  `posSemidef_mulVec_eq_zero_of_dotProduct_eq_zero`), the row combination `kernelCombo`
  (= `wᵀQv`), and — notably — a measure-free semantic-cone route for the approximate bound
  (`downward_preserve_semanticCone` on `⟨Qw,w⟩•⟨Qv,v⟩ − (wᵀQv)²`).

### §11.4–§11.8 the slice method and the graphon layer

Twenty-nine modules in three strands. The **slice strand** (`RelativePlanted` →
`RelativeCertificateGap`/`RelativePositivstellensatz` → `CertificateSliceVanishing` →
`ParametricP4Slice` → `TuranLimit` → `TuranAut` → `TuranDirac` →
`MantelNotPlantable`/`SliceRecovery` → `TuranSliceIdentities`) sits on the
§11.2–§11.3 layer; the **graphon strand** (`GraphonBasic` → `GraphonMoments` →
`GraphonRigidity`/`GraphonQuantStability`) is standalone kernel measure theory with no
flag-algebra imports; and the **`φ_W` strand** (`GraphonInducedDensity` →
`PairSubsetCount`/`EmptyTypeGraphBridge` → `GraphonHom` → `StdRootedBridge` →
`GraphonRootedDensity`/`GraphonRootedHom` → `GraphonRootedMeasure` → `GraphonKernelTransport` →
`GraphonStep`/`GraphonCounting` → `GraphonRepresentation` →
`GraphonParametricTransport`/`ParametricStabilityModulus`)
bridges the graphon strand back into the flag-algebra world — starting with the graphon→hom half
of the representation bridge (infrastructure with no single `paper.tex` display, README
Deviation 16), then, via the **rooted transport** (described in
[`HOM_TO_GRAPHON_DESIGN.md`](./HOM_TO_GRAPHON_DESIGN.md); the five modules from `StdRootedBridge`
on), running all the way to `r3_rigidity`'s a.e. kernel hypotheses (`k4freeP4_graphon_tripartite`,
the graphon-side content of `thm:k4free-p4-tripartite`, Thm 102). `GraphonRepresentation`
then closes Thm 102 itself in paper-verbatim, representative-quantified form, and
`GraphonParametricTransport` + `ParametricStabilityModulus` close the two remaining pieces the
same way — Cor 106 and Thm 112(iv). Classical inputs enter as named hypotheses throughout (README
Deviations 14a, 15b, 18); **every §11 result is formalised modulo exactly the four permanent named
classical inputs** (Erdős–Simonovits stability, Zykov's bound and its equality case,
Lovász–Szegedy existence — README [Scope & limitations](./README.md#scope--limitations)); what
remains beyond that is only the optional campaigns below. The
`ParametricP4Slice`/`SliceRecovery` certificate consumers, `TuranSliceIdentities`'s
`parametric_recovery_identities`, `GraphonKernelTransport`'s
`k4freeP4_graphon_Rtau_eq_zero`/`_Reta_eq_zero`/`_tripartite`, `GraphonRepresentation`'s
`k4free_p4_tripartite_of_represents`/`_of_rep_exists`, and
`GraphonParametricTransport`/`ParametricStabilityModulus`'s slice-consuming theorems, all carry the
Tier-2 axioms (README "Axioms assumed") — the `φ_W` strand is Tier-1 throughout except those
capstone theorems.

* **[`RelativePlanted`](./RelativePlanted.lean)** — §11.4 `def:relative-plantability` +
  `prop:relative-plantability`. The relative planted set `relQσ hc Y σ` (= `Q_σ(Y)`) and
  `RelativelyRootPlantable`; closedness by a diagonal argument (`relQσ_isClosed`),
  `relQσ_subset_Qσ`, the weak-convergence/portmanteau inclusion `support_subset_relQσ` (hence
  `relSσ_subset_relQσ`), the `Y = Q₀` recovery `relQσ_Q0_eq`/`relativelyRootPlantable_Q0_iff`,
  and part (ii): `relQσ_nonneg_implies_relEnsemble` + the equivalence
  `relative_planted_criterion`.
* **[`RelativeCertificateGap`](./RelativeCertificateGap.lean)** — §11.4
  `thm:relative-certificate-gap`. The `Y`-seminorm ε-closure (`YWithin`/`MemYClosure`), the
  relative ensemble cone `relEnsCone`, the relative master evaluation bound, the
  Stone–Weierstrass crux `relEnsCone_subset_closure_quotCone` (with the `S_σ(Y) = ∅` degenerate
  branch), and `no_relative_closed_certificate_gap`.
* **[`RelativePositivstellensatz`](./RelativePositivstellensatz.lean)** — §11.4
  `thm:relative-positivstellensatz`. Slice-valid bounds are class-valid after an `ε·1₀` shift and
  a finite quadratic penalty `M·∑ g_{j_i}²` (`relative_positivstellensatz`; compactness of `Q₀` +
  finite intersection of the sublevel sets `K_n`), and the cone form
  `relative_positivstellensatz_closure` (`Y`-non-negative = `‖·‖_{Q₀}`-closure of
  `C_{Q₀} + span{gⱼ²}`). Holds for `Y = ∅` too.
* **[`CertificateSliceVanishing`](./CertificateSliceVanishing.lean)** — §11.6
  `prop:equality-slice-vanishing`. The equality slice `eqSlice forb0 h c` and the generic mining
  principle `equality_slice_vanishing`: a class certificate `h + ∑ λᵢ ⟦ℓᵢ²⟧₀ ≤ c·1₀` forces
  `ψ(ℓᵢ) = 0` on `S_{σᵢ}(Y)` over the slice — `relative_slackness_global_sq` with `fᵢ := ℓᵢ²`,
  `n := 0`.
* **[`ParametricP4Slice`](./ParametricP4Slice.lean)** — §11.6 `thm:k4free-p4-equality-slice` +
  `thm:parametric-p4-equality-slice` (+ the hom halves of §11.8's Prop 110 / Thm 112(i)–(ii)).
  The certificate bridge: `CompleteGraphFreeP4.gap_identity` consumed through
  `equality_slice_vanishing`/`relative_slackness_*` on `parametricP4Slice r` (`parametricP4_cert`),
  yielding `parametricP4_eta_equation`/`_tau_symm`/`_tau_equation`, the extremal `K₄` density
  `parametricP4_K4_density` (Zykov as the explicit hypothesis `hZykov`), the certificate square
  bounds `parametricP4_sq_bounds`, and the approximate `K₄` density `parametricP4_K4_density_approx`
  (no Zykov input). At `r = 3` the `κ₄` coefficient vanishes, so the `k4freeP4_*` forms
  (`k4freeP4Slice`, `k4freeP4Slice_eq_parametric`) are unconditional. **Tier-2 axioms.**
* **[`TuranLimit`](./TuranLimit.lean)** — §11.5, the existence halves of `thm:turan-slice` /
  `thm:relative-mantel`. The Turán-graph flag sequence (`K_{r+1}`-free, edge density
  `→ (r-1)/r`), the balanced `r`-partite limit `exists_turan_limit`, and the nonempty slices
  `turanSlice`/`turanSlice_nonempty`, `mantelSlice`/`mantelSlice_nonempty`. The identity halves
  are delivered by the `TuranAut`/`TuranDirac`/`TuranSliceIdentities` stack below (the singleton
  claim itself — Erdős–Simonovits — enters there as the named hypothesis `hES`).
* **[`MantelNotPlantable`](./MantelNotPlantable.lean)** — §11.4 `prop:mantel-not-plantable`. The
  parity-bipartite host `knnPlusW` (`K_{n+1,n+1}` + isolated root — README Deviation 14g), the
  planted view with rooted edge density `0` (`exists_mantel_planted_view_edge_zero`), and the
  strict inclusion `mantel_not_relatively_plantable` (`relSσ ⊂ relQσ` over the Mantel slice; the
  pinning input Thm 92(i) as the explicit hypothesis `hpin` — discharged under `hES` by
  `TuranSliceIdentities`'s `mantel_not_relatively_plantable_of_uniqueness`).
* **[`SliceRecovery`](./SliceRecovery.lean)** — §11.7 `cor:parametric-p4-turan-recovery` (first
  half), `cor:k4free-p4-qualitative-stability`, `cor:parametric-qualitative-stability`.
  `parametric_recovery` (Zykov equality `hZykEq` collapses the slice to `{χ★}`; the
  "consequently" clauses are `TuranSliceIdentities`'s `parametric_recovery_identities`),
  `parametric_qualitative_stability` (+ `hne`; via `unique_slice_stability`), and
  `k4free_qualitative_stability` (the singleton identification `huniq` — Thm 102's hom avatar —
  as hypothesis). **Tier-2 axioms** on the two `parametric_*` results.
* **[`TuranAut`](./TuranAut.lean)** — §11.5 supporting layer: **Turán-graph automorphism
  transitivity** on rooted patterns. The toolkit — translation, residue-transposition lift,
  within-class swap — gives `turan_vertex_transitive` / `turan_pair_transitive`, whence all
  `σ`-labellings of a Turán flag are a single flag class:
  `labelExtensions_turan_vtype/_edge/_nonEdge_subsingleton` (the combinatorial input to the
  Dirac collapse).
* **[`TuranDirac`](./TuranDirac.lean)** — §11.5 supporting layer: **unique labellings ⟹ Dirac**.
  Finite rooting measures with a unique labelling are Dirac
  (`toProbMeasure_eq_dirac_of_subsingleton`); weak-limit transfer via Mathlib's `diracProba`
  closed embedding (`extend_eq_dirac_of_labelExtensions_subsingleton`), collapsing the relative
  support of a singleton constraint set (`relSσ_singleton_of_extend_dirac`); and the fixed
  choice `turanLimit`/`turanSubseq`/`turanLimit_spec`/`turanLimit_mem_slice` of the balanced
  `r`-partite limit with its subsequence exposed.
* **[`TuranSliceIdentities`](./TuranSliceIdentities.lean)** — §11.5 `thm:turan-slice` /
  `thm:relative-mantel`, the **identity halves**. Canonical labellings of the Turán flags,
  single-root extension counts, the singleton supports with pinned values
  `turanLimit_relSσ_vtype/_edge/_nonEdge`, and — under the named Erdős–Simonovits hypothesis
  `hES` — `turan_slice_identity_vtype/_edge/_nonEdge` and `relative_mantel_vtype` (Thm 92(i));
  `mantel_not_relatively_plantable_of_uniqueness` (Prop 86 with `hpin` discharged) and
  `parametric_recovery_identities` (Cor 105's "consequently" clauses; **Tier-2**, inherited via
  `parametric_recovery` — README Deviation 15).
* **[`GraphonInducedDensity`](./GraphonInducedDensity.lean)** — the `φ_W` analytic layer;
  infrastructure, no single `paper.tex` display (README Deviation 16). `graphonFlagDensity W G`
  (the probability that a `W`-random graph on `|G|` uniform samples equals `G` exactly), built
  from the pointwise `inducedWeight`/`adjWeight` product over strictly-increasing vertex pairs;
  relabelling invariance `graphonFlagDensity_comap_equiv` (a measure-preserving change of
  variables, `volume_measurePreserving_piCongrLeft`); the **extension partition**
  `graphonFlagDensity_extension_sum` (the density on `Fin n` is the sum over all `Fin ℓ`
  restrictions, via a `Finset.prod_add` partition of unity over the new pairs and
  `volume_preserving_piEquivPiSubtypeProd` marginalisation); the **block product**
  `graphonFlagDensity_block_mul` (the analogous identity for two disjoint blocks, via
  `volume_measurePreserving_sumPiEquivProdPi` + `integral_prod`); and the closing identities
  `sum_graphonFlagDensity = 1` and `graphonFlagDensity_top_two = W.edgeDensity`.
* **[`PairSubsetCount`](./PairSubsetCount.lean)** — the two-flag analogue of `LabeledCount`,
  needed because multiplicativity is a *joint* statement about two flags. `IsInducedPairOn` (two
  vertex subsets, each containing the roots, disjoint outside them, each inducing one of the two
  flags) and `flagDensity₂_eq_subset_count_div` (the pair density as the count of such subset
  pairs over the multinomial coefficient); the base-library `flagDensity₂`/`labeledGraphPairToList`
  machinery is reused as-is, only this pair-counting bridge is new.
* **[`EmptyTypeGraphBridge`](./EmptyTypeGraphBridge.lean)** — unlabelled flags as plain graphs.
  `flagEqv_emptyType_iff`/`graphFlag_eq_iff` (at `∅ₜ`, flag isomorphism is graph isomorphism —
  the `type_preserve` law is vacuous on `Fin 0`); `graphFlag_out`/`graphFlag_surjective`; the
  relabelling equivalence `graphComapEquiv`/`graphFlag_comap_equiv`; the **permutation toolkit**
  `exists_perm_comp_emb`/`exists_perm_comp_emb_pair` (any two embeddings, resp. disjoint pairs of
  embeddings, of `Fin n` into `Fin ℓ` differ by a permutation of `Fin ℓ` — built from
  `Equiv.ofInjective` on the ranges plus `Fintype.equivOfCardEq` on the complements) — the
  reindexing engine `GraphonHom`'s subset-averaging runs on; and the subset-count specialisations
  `flagDensity₁_graphFlag`/`flagDensity₂_graphFlag` (unlabelling `LabeledCount`/`PairSubsetCount`'s
  general-`σ'` results to `∅ₜ`).
* **[`GraphonHom`](./GraphonHom.lean)** — the capstone: **every graphon is a positive
  homomorphism**. The profile `graphonProfileFun W F = ∑_{H, ⟦H⟧=F} graphonFlagDensity W H` and
  `graphonProfile W : FlagDensitySpace ∅ₜ`; the three structural properties
  `graphonProfile_oneProp` (the unique graph on `Fin 0`), `graphonProfile_zeroSpaceProp` (the
  chain rule, via `graphonFlagDensity_extension_sum` + subset-averaging over
  `exists_perm_comp_emb`), and `graphonProfile_mulProp` (multiplicativity, via
  `graphonFlagDensity_block_mul` + `exists_perm_comp_emb_pair`); the assembled homomorphism
  `graphonHom W : PositiveHom ∅ₜ` (via `positiveHomFromZeroSpaceOneMulProp`, the same pattern
  `ComplementHom`'s `complHom` used) with its point `graphonHomPoint`; and the sanity link
  `graphonHom_edge : φ_W(unlabelledEdgeFlag) = W.edgeDensity` tying this flag-algebra-side
  construction back to the `GraphonBasic` kernel layer.
* **[`StdRootedBridge`](./StdRootedBridge.lean)** — the rooted-transport foundation described in
  [`HOM_TO_GRAPHON_DESIGN.md`](./HOM_TO_GRAPHON_DESIGN.md): the two-root analogue of
  `EmptyTypeGraphBridge`. Standard-rooted graphs at a two-vertex type
  (`RootCompatible`/`mkStdRooted`, roots at `0, 1` via `Fin.castLE`), flag equality iff
  root-fixing isomorphism (`mkStdRooted_flag_eq_iff`), standard-rooted representatives
  (`exists_stdRooted_rep`), the root-fixing permutation engine
  (`exists_rootfix_perm_comp_emb(_pair)`), and the rooted density-as-subset-count formula
  (`flagDensity₁_stdRooted`). Certificate-free (general `σ : FlagType (Fin 2)`); feeds
  `GraphonRootedDensity`/`GraphonRootedHom`.
* **[`GraphonRootedDensity`](./GraphonRootedDensity.lean)** — the
  unnormalised rooted density `unnormRootedDensity` (induced weight with the root coordinates
  pinned at `u, v` via `pinRoots`), the root factor `rootWeight`/`RootAdmissible`,
  root-fixing relabelling invariance, the rooted extension partition, total mass
  `sum_unnormRootedDensity = rootWeight`, the glued block product
  `unnormRootedDensity_block_mul` (glue embeddings `Fin.castLE`/`glueEmb₂` overlapping
  exactly in the shared roots — whence the single surviving `rootWeight` factor), and the
  subset↔embedding bridge (`exists_rootFixing_emb_range`, `stdRooted_subset_iso_iff`).
* **[`GraphonRootedHom`](./GraphonRootedHom.lean)** — **the rooted
  conditional homomorphism**. The conditional profile `graphonRootedProfileFun` (sum over the
  standard-rooted class, divided by `rootWeight`) satisfies `zeroSpaceProp` (root-fixing
  subset-averaging with the `C(ℓ−2, n−2)` count), `oneProp` (needs `RootAdmissible`), and
  `mulProp` (the glued block product; at the tight glued size the second subset of a valid
  pair is forced to be the complement-plus-roots of the first, collapsing the pair count),
  assembling to `graphonRootedHom W σ' u v h : PositiveHom σ'` — the view of `φ_W` from a
  `W`-random root pair — with joint measurability in `(u, v)` for the rooted-view measure of
  [`GraphonRootedMeasure`](./GraphonRootedMeasure.lean) below.
* **[`GraphonRootedMeasure`](./GraphonRootedMeasure.lean)** — **the
  rooted-view measure is the extension measure**. `rootMass`/`rootMass_eq_typeFlag` (the total
  root-factor mass is `φ_W`'s value on the two-vertex type flag), `integral_unnormRootedDensity`
  (integrating out the pinned coordinates recovers the unrooted `graphonFlagDensity`), the
  **rooted-vs-unrooted counting bridge** `card_stdRooted_class` (the standard-rooted class count
  is `downwardNormalizingFactor` times the unlabelled class count — a same-size double count over
  `(graph, root-placement)` pairs, the degenerate-`n₀` analogue of
  `FlagOperators.isoInjectiveMapSet`, via the private `RootCompatibleAt`/`mkRootedAt` machinery
  generalising `RootCompatible`/`mkStdRooted` to an arbitrary root embedding), the bridge integral
  identity `integral_rootedClassSum`, and the capstone
  `rootedViewMeasure`/**`rootedViewMeasure_eq_extend`**: the normalised `rootWeight`-weighted
  pushforward of `graphonRootedHom` equals `ℙ[graphonHom W]`, via `measure_eq_of_integral_flag_eq`.
* **[`GraphonKernelTransport`](./GraphonKernelTransport.lean)** — **the capstone**: the **kernel
  dictionary** — `graphonRootedHom_a_tau`/`_b_tau`/`_g_tau`/
  `_z_eta`/`_g_eta`, the rooted three-vertex flag values as `deg`/`codeg` expressions
  (each a single standard-rooted graph on `Fin 3`, since a root-fixing
  permutation of `Fin 3` is forced to be the identity) — and the **transport**:
  `k4freeP4_graphon_Rtau_eq_zero`/`_Reta_eq_zero` push the `K₄`-free `P₄`-slice equations of
  `ParametricP4Slice` (holding on `relSσ k4freeP4Slice`, hence `ℙ[φ_W]`-a.e. via
  `support_subset_relSσ`, hence `rootWeight`-a.e. on `I × I` via `rootedViewMeasure_eq_extend`)
  through the dictionary into `Rtau_eq_zero_iff_ae`/`Reta_eq_zero_iff_ae`'s hypothesis shape;
  assembling to **`k4freeP4_graphon_tripartite`**: any graphon whose `φ_W` lies in the `K₄`-free
  `P₄`-slice (with both root types of positive mass) is a.e. the balanced complete tripartite
  graphon — `Graphon.r3_rigidity` with both hypotheses discharged, the graphon-side content of
  `thm:k4free-p4-tripartite` (Thm 102). **Tier-2** on these three theorems (they consume the
  slice equations); the dictionary lemmas are Tier-1.
* **[`GraphonStep`](./GraphonStep.lean)** — **step graphons**.  The
  equal-`N`-cell map `cellIdx` (floor-based, clamped at `x = 1`; measurable, fibres of volume
  exactly `1/N`), the indicator kernel `stepGraphon hN G`, and the pointwise indicator
  identity `inducedWeight_stepGraphon`: the induced weight of `H` at samples `c` is the
  indicator of the *literal* graph equality `G.comap (cellIdx ∘ c) = H`.  Tier-1.
* **[`GraphonCounting`](./GraphonCounting.lean)** — the counting lemma `graphonProfileFun_stepGraphon_sub_le` with
  explicit error `n(n−1)/N` (exact tuple-count formula `profile = #{realising cell
  tuples}/Nⁿ`, injective tuples ↔ `n!` times the subset count of `flagDensity₁_graphFlag`,
  non-injective mass and falling-factorial defect each `≤ C(n,2)/N`), and **density of the
  graphon-hom range**: `exists_graphonHomPoint_seq_tendsto` — every `φ : PositiveHom ∅ₜ` is
  a limit of `graphonHomPoint` points.  With `positiveHomSpace_isClosed`, the representation
  theorem is equivalent to `IsClosed (Set.range graphonHomPoint)`.  Tier-1.
* **[`GraphonRepresentation`](./GraphonRepresentation.lean)** — closes Thm 102 by composing
  profile agreement with the kernel-transport result, bypassing the closedness route above (an
  honest martingale-limit proof of that route was costed at 1500–3000+ lines with no Mathlib
  precedent). `posHomPoint_eq_of_graphonProfileFun_eq`
  (profile agreement gives point agreement) composes with `k4freeP4_graphon_tripartite` to give
  **`k4free_p4_tripartite_of_represents`** — the unconditional, **paper-verbatim** `thm:k4free-p4-tripartite`
  (Thm 102): every graphon *representing* a point of the slice is a.e. balanced tripartite, no
  representation-existence input needed since the paper's own quantifier runs over representatives
  — and **`k4free_p4_tripartite_of_rep_exists`**, the existence form conditional on the one named
  classical input `hrep : ∀ φ₀, ∃ W, ∀ F, graphonProfileFun W F = φ₀.coe F` (Lovász–Szegedy
  existence; `hrep` is equivalent to `IsClosed (Set.range graphonHomPoint)` given
  `exists_graphonHomPoint_seq_tendsto` above, so retiring it is the deferred weak-regularity
  campaign). Tier-2 (consumes `k4freeP4_graphon_tripartite`); `Graphon.slice_rigidity` alone has no
  rooted-transport counterpart for Cor 106 — that counterpart is supplied by
  `GraphonParametricTransport` below.
* **[`GraphonParametricTransport`](./GraphonParametricTransport.lean)** — the
  general-`r` mirror of the rooted-transport stack, closing **Cor 106**
  (`cor:top-endpoint-recovery`) the same way as Thm 102. The general-`r` rooted transports
  `parametricP4_graphon_Rtau_eq_zero`/`_Reta_eq_zero` (mechanical `r`-generalisations of the
  `r = 3` ones); the **`R_τ⁻` kernel functional** `Graphon.RtauMinus := ∫∫W(x,y)(d(x)−d(y))²`
  with its a.e. characterisation; the **`f₂` hom→kernel bridge** `graphonHom_f₂_eq_RtauMinus :
  φ_W(f₂) = R_τ⁻(W)` (via the extension-measure spec at the edge type — no new density
  computations), which discharges the kernel-level third clause of Thm 112(i)
  (`parametricP4_graphon_RtauMinus_le`/`_eq_zero`, Prop 110); the kernel-level Cor 106
  `parametricP4_graphon_top_endpoint_rigidity` (slice membership + the scalar pin
  `edgeDensity = α_r⁺` — in place of the Zykov equality case — force the balanced complete
  `r`-partite graphon via `Graphon.slice_rigidity`); and, composing with profile agreement as in
  `GraphonRepresentation`, **`parametricP4_top_endpoint_of_represents`** / `_of_rep_exists`. Stated
  at `3 ≤ r` (the paper's `r ≥ 4`, since `r = 3` is already unconditional — Deviation 15c). Tier-2
  on the slice-consuming theorems.
* **[`ParametricStabilityModulus`](./ParametricStabilityModulus.lean)** — closes
  **Thm 112(iv)** (the `ω_Zyk` route). `parametric_stability_via_modulus` (hom level) and
  `parametric_graphon_stability_via_modulus` (the graphon-facing instantiation), in the same
  modulus-abstraction pattern as `GraphonQuantStability.stability_via_modulus`'s `ω_Tur` route: the
  certificate deficit `Δ ≤ p₀(r)·ω` forces the `K₄` density within `ω` of extremal
  (`parametricP4_K4_density_approx`), triggering the assumed modulus `hmod`. Notably, **the Zykov
  bound hypothesis `hZykov` is not needed at all** — the `K₄`-density approximation drops the
  certificate's Zykov term without using its sign, so `hmod` is the only classical content. Tier-2
  (consumes `parametricP4_K4_density_approx`).
* **[`GraphonBasic`](./GraphonBasic.lean)** — §11.7 preliminaries. The `Graphon` structure
  (symmetric measurable `[0,1]`-kernel on `unitInterval`), `deg`/`codeg`,
  `edgeDensity`/`degSq`/`triDensity`, measurability/boundedness/integrability, and the two Fubini
  identities the moment computations run on.
* **[`GraphonMoments`](./GraphonMoments.lean)** — §11.7 `thm:parametric-moments` + §11.8
  `thm:approximate-moments`. The local errors `ellEta`/`ellTau`, square averages `Reta`/`Rtau`
  (with the a.e. characterisations `Rtau_eq_zero_iff_ae`/`Reta_eq_zero_iff_ae`), the master moment
  identity, the certificate-free approximate theorems `approximate_moments(_interval/_variance)`,
  and the exact identities `moments_T`/`_D`/`_variance`/`_interval`/`_regular_iff` as the
  `R = 0` instance.
* **[`GraphonRigidity`](./GraphonRigidity.lean)** — §11.7 `thm:slice-rigidity` + `cor:r3-rigidity`.
  The ladder `rigid_deg_ae` → `rigid_codeg_ae` → `rigid_sections_boolean` → `slice_rigidity`
  (the measurable partition `P : I → Fin r`, fibers `1/r`, `W = 0/1` by block a.e. — README
  Deviation 14c), with the colour classes grown by the Markov-selection trick; `r3_rigidity` is
  the hypothesis-free `r = 3` case.
* **[`GraphonQuantStability`](./GraphonQuantStability.lean)** — §11.8 kernel-level quantitative
  stability (`thm:k4free-p4-quant-stability`, `thm:parametric-quant-stability` (iii)).
  `quadratic_confinement`/`moment_deviation_bound`, both interval-localisation halves
  (`interval_localisation`, `interval_localisation_below`, `r ≥ 4`), the `r = 3` chain
  (`r3_edge_sq_bound`, `r3_degree_concentration`, `r3_edge_density_stability`,
  `r3_certificate_instance`), and `stability_via_modulus` (`ω_Tur` abstracted over the target
  predicate; the `r ≥ 4` `ω_Zyk` route of Thm 112(iv) is the separate
  [`ParametricStabilityModulus`](./ParametricStabilityModulus.lean) module above — its docstring
  was updated in place to point there). The `R`-bounds enter as hypotheses at this `r = 3` level
  (README Deviation 14b); the general-`r` `R_τ⁻` functional is defined in
  [`GraphonParametricTransport`](./GraphonParametricTransport.lean) above.

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

### The §6–§7 capstone (`subst_root_plantable`)

`subst_root_plantable` (in [`SubstitutionClosed`](./SubstitutionClosed.lean)) follows the **same six
steps**, with three substitutions: (i) the base graph is fed to a *within-class blow-up closure*
hypothesis to obtain a family `Wf` with `subBlowup Γ (Wf M) ∈ class` for every `M` (replacing
`clone_closed`); (ii) the blow-up sequence is `blowupFlagSeq_sub Γ Wf` and the cylinder-mass crux is
`planted_cylinder_mass_sub`, using `planted_estimate_sub` / `planted_mass_sub` /
`embeddingEquivBlowupEmbeddings_sub` in place of their §5 namesakes; (iii) steps 4 and 6
(weak convergence, Portmanteau + support) are **identical** — they never mention the construction.
The three end results instantiate the closure hypothesis: `true_clone_root_plantable` with `W = ⊤`,
`substitution_root_plantable` with in-class fibres, and `cluster_root_plantable` via
`clusterClass_trueCloneClosed`.

### The §8 capstone (`finitePlanting_root_plantable`)

`finitePlanting_root_plantable` (in [`FinitePlanting`](./FinitePlanting.lean)) follows the **same six
steps**, but the construction is now *abstract*. Step 1 (reduce to finite cylinders) is unchanged
(`mem_closure_of_forall_finset_cylinder`). Step 2 (the in-class base sequence) is again
`exists_constrained_flagSeq_limit`. The change is in steps 3 and 5:

* **Step 3 (sequence + base limit).** There is no fixed base blown up over `M`. Instead, applying the
  `FinitePlanting` hypothesis to each large representation term `(Gₜ, θₜ)` yields a graph `Hₜ` with a
  planting `Θₜ`; the `Hₜ` (sizes `→ ∞`) are assembled into a flag sequence (strictly-increasing-size
  subsequence via `strictMono_subseq_of_tendsto_atTop`, then `increasing_flagSeq_contain_convergent_subseq`),
  whose limit `φ₀` lies in `Q₀` by the *generic* `flagSeqLimit_mem_Q0` (each `Hₜ` is in the class,
  hence forbidden-free), and has `φ₀⟨σ⟩₀ > 0` from the uniform bound `subgraphDensity σ Hₜ ≥ δ`
  (derived from `|Θₜ| ≥ δ|V(Hₜ)|^k` by embedding↔`subgraphCount` counting).
* **Step 5 (cylinder mass — now immediate).** With `C̃` centred at `ψ` (radius `2ε/3`), each
  `θ̂ ∈ Θₜ` gives a labelling whose profile lies in `C̃` (clause (iii) of `FinitePlanting` + the
  representation closeness), and `toProbMeasure_apply_eq_labeling_ratio` + `card_labelings_eq_card_embeddings`
  give `Pₜ(C̃) ≥ |Θₜ|/|V(Hₜ)|^k ≥ δ` directly — **no** `planted_estimate`/`ρ`/`BinomialRatio`.

Steps 4 and 6 (weak convergence via `tendsto_rootingMeasure_extend`; Portmanteau + support) are again
**identical** — they never mention the construction. The `C₅`-free end results
`c5free_one_root_plantable`/`c5free_two_root_nonedge_plantable` then arrive in two hops:
`SparseRootRepair ⇒ FinitePlanting` (`sparseRootRepair_finitePlanting`) and the `C₅`-free sparse-repair
instances supply the hypothesis, with `lem:c5-nbhd` bounding the repaired-edge count.

---

## Formalisation frontier / what remains

This directory formalises `paper.tex` **§1–§10 in full** — including the whole obstruction half:
`thm:pinning` (Theorem 53, `pinning_obstruction`); `lem:complementation` (Lemma 50), the
complementation invariance of root-plantability, formalised as `complementation_invariance` (the
`FlagComplement` → `ComplementHom` → `ComplementClass` → `ComplementInvariance` stack — via the
complement *homeomorphism* of homomorphism spaces, not the paper's flag-algebra complement
isomorphism); the §9.4 boundary / no-interior theorem `thm:no-interior` (Theorem 55,
`no_interior_pinning`, the `NoInterior` → `EdgeThinning` → `EdgeThinningLimit` → `NoInteriorThinning`
edge-thinning stack — McDiarmid-free, README Deviation 10); and the §9.5 `C₅`-edge obstruction
`thm:c5-edge-not-root-plantable` (Theorem 62, `c5free_edge_not_rootPlantable`, the
`C5FewTriangles` + `C5EdgeObstruction` pair) with `lem:c5-few-triangles` and the book-graph quotient
point. **`lem:complementation` is formalised** (this overrides any stale note to the contrary
elsewhere). **§10 is formalised in full** (`sec:empty-type`, Prop 64–Cor 70: the empty-type collapse
`prop:empty-type`/`cor:confined`, the closed-cone equality `thm:no-closed-certificate-gap`, the
vanishing ideal `prop:ideal-zero`, the single-point collapse `prop:single-point`, and the `C₅`-edge
inertness `cor:c5-edge-closed-inert` — the `DownwardAverage`/`EmptyTypeCollapse`/`CertificateCones`/
`VanishingIdeal`/`BooleanPoint`/`SinglePoint`/`C5EdgeInert` modules, README Deviation 12).
**The §11.2–§11.8 relative (slice) theory is formalised** — §11.2–§11.3 (Lemma 71–Proposition 82:
the relative support `S_σ(Y)` with `lem:relative-closure`/`prop:relative-soundness`/
`prop:relative-criterion`, and the complementary-slackness principle `thm:relative-slackness`/
`lem:relative-cauchy-schwarz`/`cor:sos-first-moments`/`thm:kernel-slackness`/
`prop:unique-slice-stability` — the `RelativeSupport`/`RelativeClosure`/`RelativeSlackness`/
`KernelSlackness` modules, README Deviation 13; §11.1 is prose), **and §11.4–§11.8** (the slice
method and the graphon layer: all of §11.4 — `def:relative-plantability`/
`prop:relative-plantability`/`prop:mantel-not-plantable`/`thm:relative-certificate-gap`/
`thm:relative-positivstellensatz`; `thm:turan-slice`/`thm:relative-mantel` — existence
unconditional, the identity halves under the named Erdős–Simonovits hypothesis `hES` via the
transitivity→Dirac route;
`prop:equality-slice-vanishing` and the `P₄` slice theorems `thm:k4free-p4-equality-slice`/
`thm:parametric-p4-equality-slice`; the kernel-level `thm:parametric-moments`/`thm:slice-rigidity`/
`cor:r3-rigidity`/`thm:approximate-moments`/`thm:k4free-p4-quant-stability`/
`thm:parametric-quant-stability`(i)–(iii); and the corollaries Cor 104/105/107, Cor 105 complete
including its "consequently" identities — the
`RelativePlanted`/`RelativeCertificateGap`/`RelativePositivstellensatz`/`CertificateSliceVanishing`/
`ParametricP4Slice`/`TuranLimit`/`MantelNotPlantable`/`SliceRecovery`/
`TuranAut`/`TuranDirac`/`TuranSliceIdentities` +
`GraphonBasic`/`GraphonMoments`/`GraphonRigidity`/`GraphonQuantStability` modules, README
Deviations 14–15 — classical inputs as named hypotheses, Tier-2 axioms on the certificate
consumers). **The graphon→hom half of the representation bridge is formalised as
infrastructure**: every graphon `W` is a positive homomorphism `φ_W : PositiveHom ∅ₜ`
(`graphonHom`, [`GraphonHom`](./GraphonHom.lean)), built via the induced flag density
([`GraphonInducedDensity`](./GraphonInducedDensity.lean)) and the subset-count bridges
([`PairSubsetCount`](./PairSubsetCount.lean), [`EmptyTypeGraphBridge`](./EmptyTypeGraphBridge.lean)),
with the sanity link `graphonHom_edge` to `GraphonBasic.edgeDensity` — no single `paper.tex`
display (README Deviation 16). **The rooted transport described in `HOM_TO_GRAPHON_DESIGN.md`
is complete**: the five-module stack `StdRootedBridge`/
`GraphonRootedDensity`/`GraphonRootedHom`/`GraphonRootedMeasure`/`GraphonKernelTransport` carries
the `K₄`-free `P₄`-slice equations, through the rooted conditional homomorphism and the measure
identification `rootedViewMeasure_eq_extend` (= `ℙ[φ_W]`), into `r3_rigidity`'s a.e. kernel
hypotheses, discharging both of them for any graphon in the slice
(`k4freeP4_graphon_tripartite`) — the graphon-side content of `thm:k4free-p4-tripartite`
(Thm 102). **[`GraphonRepresentation`](./GraphonRepresentation.lean) then closes Thm 102 itself**:
`k4free_p4_tripartite_of_represents` is the unconditional, paper-verbatim
statement (quantified over *representing* graphons — the paper's own quantifier shape, so no
representation-existence input is needed), plus `k4free_p4_tripartite_of_rep_exists` conditional
on the one named classical input `hrep` (Lovász–Szegedy existence). The same route closes
**Cor 106**
([`GraphonParametricTransport`](./GraphonParametricTransport.lean),
`parametricP4_top_endpoint_of_represents`/`_of_rep_exists`) and **Thm 112(iv)**
([`ParametricStabilityModulus`](./ParametricStabilityModulus.lean),
`parametric_stability_via_modulus`, which turns out not to need the Zykov bound hypothesis at
all). **Every numbered result of §11 is now formalised**, modulo exactly the four permanent named
classical inputs below.

Not yet formalised — first, **four classical results the paper itself cites as unproved external
inputs, by permanent design decision** (never intended to be proved inside this development):

* **Erdős–Simonovits stability** (the singleton claim of Thm 91/92): the identity halves
  of `thm:turan-slice` / `thm:relative-mantel` **are** formalised (the
  `TuranAut`/`TuranDirac`/`TuranSliceIdentities` transitivity→Dirac stack, discharging
  `MantelNotPlantable`'s `hpin`), with ES entering only as the named hypothesis `hES` —
  equivalent to the paper's "exactly one point" via `turanLimit_mem_slice`;
* **Zykov's `K₄`-density bound** (`r ≥ 4`, `hZykov`) and its **equality case** (`hZykEq`) — the
  paper's own §11 standing paragraph names both as external inputs (README Deviation 18);
* **Lovász–Szegedy existence** (`hrep`) — the one hypothesis of the four with a costed, optional
  retirement path: the weak-regularity campaign of `HOM_TO_GRAPHON_DESIGN.md` (module plan
  `GraphonMartingaleLimit` — sequential compactness of the graphon space via Doob martingale
  convergence, est. 1500–3000+ lines, no Mathlib precedent — not attempted here). Absent that
  campaign, `hrep` is exactly the hypothesis behind every `_of_rep_exists` corollary above.

Not yet formalised (future work, all optional — the machinery here is intended to be reusable for
any of it):

* the pinning **conjecture** `conj:characterisation` (the tentative general characterisation) — the
  one §9 result still open;
* **§12** is open problems — prose, nothing to formalise;
* within `cor:degenerate-family`, the **three non-`C₄` families** — general `K_{s,t}` (`s ≥ 3`), even
  cycles `C_{2k}`, and planar graphs — whose extremal edge bounds (Kővári–Sós–Turán,
  Bondy–Simonovits, the planar `≤ 3n−6` bound) lie outside current Mathlib. Only the abstract
  subquadratic criterion `edgeDegenerate_of_subquadratic` is proved; `C₄` (the `K_{2,2}` case) is the
  one whose bound is established from scratch and discharged through that criterion;
* **optional campaigns with no open correctness gap behind them**: Phase 3 (a kernel-level
  Mantel/Turán uniqueness theorem that would let `hES` be discharged through the graphon⟷hom
  bridge) and, again, the Kővári–Sós–Turán-type extremal bounds above.
