# MetaTheory — a Lean 4 formalisation of the root-plantability meta-theory of flag algebras

This directory formalises, in Lean 4 (toolchain `leanprover/lean4:v4.27.0`, Mathlib `v4.27.0`),
the **proved results of Sections 1–8 of [`paper.tex`](./paper.tex)**, plus the first abstract
obstruction theorem from §9 — the *meta-theory* of flag algebras that asks **when
forbidden-subgraph ("quotient") reasoning is complete** for a constrained graph class.

The headline result is:

> **`clone_root_plantable`** ([`CloneClosed.lean`](./CloneClosed.lean)) — every clone-closed
> hereditary graph class is *root-plantable*: for a non-degenerate type `σ`, the supported space
> `S_σ` equals the quotient space `Q_σ`. Consequently quotient semantics and ensemble semantics
> agree for **every** `f ∈ A^σ`. Specialised to `K_r`-free graphs, this is **`cor:clique-free`**
> (`clique_free_root_plantable` / `clique_free_quotient_iff_ensemble`), covering the
> triangle-free case `r = 3`.

The same conclusion holds for classes closed under **complete blow-ups** (true twins, §6),
**substitution** (§7), and cluster graphs — and §5, §6 and §7 are in fact **one theorem**:

> **`blowupClosed_root_plantable`** ([`BlowupClosed.lean`](./BlowupClosed.lean), paper
> `thm:blowup-root-plantable`) — every **blow-up-closed** hereditary class is root-plantable.
> A class is *blow-up-closed* if one may always blow up a single vertex of a member to an
> arbitrarily large graph, *choosing* the interior, without leaving the class (`BlowupClosed`).

Clone-closed (§5, `clone_root_plantable_blowup`), true-clone-closed (§6, `true_clone_root_plantable`,
with `cluster_root_plantable`), and substitution-closed (§7, `substitution_root_plantable`) are each
a one-line corollary, via the corresponding `…toBlowupClosed` implication. Blow-up-closure is the
*existential* ("some interior works") weakening of substitution-closure's *universal* ("every
interior works") — strictly weaker, so unlike substitution-closure it covers §5 and §6 as well.

**§8 goes beyond global closure**, with a *finite, local* root-plantability criterion and its first
non-closure application:

> **`finitePlanting_root_plantable`** ([`FinitePlanting.lean`](./FinitePlanting.lean), paper
> `thm:finite-local-planting`) — if a hereditary class has the **finite planting property** at a
> non-degenerate `σ` (every large in-class `σ`-flag can be replaced by a larger in-class graph with
> a positive-density set of `σ`-embeddings whose bounded-size flag densities match), then it is
> root-plantable. This is the §5/§7 capstone argument with the blow-up sequence replaced by an
> *abstract* planting family — so the dense, **not blow-up-closed** `C₅`-free class qualifies via a
> sparse local repair (`sparseRootRepair_finitePlanting`), giving `c5free_one_root_plantable`
> (`S₁ = Q₁`) and `c5free_two_root_nonedge_plantable` (`S_η = Q_η`).

**§9 (obstructions), §9.1 and §9.2 are formalised** — the "negative" side, where quotient reasoning
is *strictly stronger* than ensemble reasoning:

> **`pinning_obstruction`** ([`Pinning.lean`](./Pinning.lean), paper `thm:pinning`) — if a
> labelled quantity is almost surely pinned to one value under every admissible random extension,
> but some quotient point takes a different value, then `S_σ ≠ Q_σ`.  Its concrete instances are the
> **degeneracy obstruction** `degenerate_not_rootPlantable` (`thm:degenerate-obstruction`) and the
> dual **dense obstruction** `coDegenerate_not_rootPlantable` (`cor:codegenerate`): the one-root edge
> density is boundary-pinned to `0` (resp. `1`) across all constrained limits, while a star (resp.
> co-star) realises the opposite boundary in `Q_vtype`.  The `C₄`-free class
> (`c4free_not_rootPlantable`, `lem:c4-edge-zero`) and its dense complement
> (`coC4free_not_rootPlantable`) are explicit such classes.

The remaining §9 subsections (`thm:pinning`'s `conj:characterisation`, the boundary/no-interior
results `subsec:boundary`, the `C₅`-edge obstruction `sec:c5-edge`) and the full complementation
*isomorphism* `lem:complementation` are not formalised — see [Scope & limitations](#scope--limitations).

Everything here is **machine-checked and `sorry`-free**: "a result is verified" means the Lean
kernel accepts its proof with no `sorry`, `admit`, `native_decide`, or new `axiom`.

For the dependency structure and a module-by-module map see **[`ARCHITECTURE.md`](./ARCHITECTURE.md)**;
for conventions and a suggested reading order see **[`READING_GUIDE.md`](./READING_GUIDE.md)**.

---

## What is formalised

| Paper result | Statement (informal) | Lean name | Module |
|---|---|---|---|
| §2 `lem:support-as` | a.s. non-negativity ⇔ non-negativity on the support | `ae_nonneg_iff_nonneg_on_support` | [`MeasureSupport`](./MeasureSupport.lean) |
| §3 (quotient algebra) | the constrained algebra `A^σ[T₁]`, the supported space `Q_σ`, and `χ ∈ Q_σ ⇔ χ` vanishes on forbidden flags | `ConstrainedAlgebra`, `Qσ`, `mem_Qσ_iff`, `Qσ_isClosed` | [`ConstrainedClass`](./ConstrainedClass.lean) |
| §3 (faithfulness) | heredity ⟹ the forbidden ideal is the ℝ-span of the forbidden flags | `forbiddenIdeal_eq_span` | [`ForbiddenIdeal`](./ForbiddenIdeal.lean) |
| §3 `lem:support-passes-general` | a random extension of a constrained limit is a.s. constrained: `supp ℙ[φ₀] ⊆ Q_σ` | `support_passes` | [`SupportClosure`](./SupportClosure.lean) |
| §4 `def:root-planting` | `S_σ` (closure of supports of admissible extensions); root-plantable ⇔ `S_σ = Q_σ` | `Sσ`, `RootPlantable` | [`SupportClosure`](./SupportClosure.lean) |
| §4 `thm:support-criterion` | quotient ⇔ ensemble non-negativity for **every** `f` iff root-plantable | `support_criterion` | [`SupportClosure`](./SupportClosure.lean) |
| §5 `def:independent-blow-up` | the independent blow-up `G^m`, its projection, `K_r`-freeness preservation | `independentBlowup`, `cliqueFree_independentBlowup` | [`Blowup`](./Blowup.lean) |
| §5 `lem:planted-mass` | a uniform induced embedding of `σ` is *planted* with probability `≥ (λ/2k)^k` | `planted_mass` | [`Blowup`](./Blowup.lean) |
| §5 `lem:planted-estimate` | (equal non-root clones) planted vs base density differ by `≤ 1 − ρ` | `planted_estimate` | [`PlantedEstimate`](./PlantedEstimate.lean) |
| §5 `thm:clone-root-plantable` | clone-closed hereditary classes are root-plantable | `clone_root_plantable` | [`CloneClosed`](./CloneClosed.lean) |
| §5 `cor:clique-free` | `K_r`-free / triangle-free classes are root-plantable | `clique_free_root_plantable`, `clique_free_quotient_iff_ensemble` | [`CloneClosed`](./CloneClosed.lean) |
| §6 `def:complete-blow-up` | the complete blow-up `G^{m,+}` (clique clone classes); the generalised blow-up `subBlowup` | `completeBlowup`, `subBlowup` | [`SubstitutionBlowup`](./SubstitutionBlowup.lean) |
| §6 `lem:true-planted-estimate`, §7 `lem:general-planting-estimate` | the planted mass + estimate carry over to *any* blow-up (the interior is never observed) | `planted_mass_sub`, `planted_estimate_sub` | [`SubstitutionEstimate`](./SubstitutionEstimate.lean) |
| §6 `thm:true-clone-root-plantable` | true-clone-closed hereditary classes are root-plantable | `true_clone_root_plantable`, `true_clone_quotient_iff_ensemble` | [`TrueClone`](./TrueClone.lean) |
| §6 `cor:cluster-graphs` | cluster graphs (`P₃`-free; not clone-closed) are root-plantable | `cluster_root_plantable`, `cluster_quotient_iff_ensemble` | [`ClusterGraph`](./ClusterGraph.lean) |
| §7 `def:substitution-closed` | the substitution `G[H_v]` (= `subBlowup G H`) | `subBlowup`, `SubstitutionClosed` | [`SubstitutionBlowup`](./SubstitutionBlowup.lean), [`Substitution`](./Substitution.lean) |
| §7 `def:blow-up-closed`, `def:vertex-blowup` | the single-vertex blow-up `G[v→H]`; the blow-up-closure property | `oneBlowup`, `BlowupClosed` | [`BlowupClosed`](./BlowupClosed.lean) |
| §7 `lem:blowup-iterate` | single-vertex blow-up closure ⟹ uniform full blow-up in the class | `BlowupClosed.toUniform` | [`BlowupClosed`](./BlowupClosed.lean) |
| §7 `thm:blowup-root-plantable` | **the unified theorem**: blow-up-closed hereditary classes are root-plantable | `blowupClosed_root_plantable` | [`BlowupClosed`](./BlowupClosed.lean) |
| §7 `cor:closures-imply-blowup` | clone- / true-clone- / substitution-closed ⟹ blow-up-closed | `GraphClass.toBlowupClosed`, `TrueCloneClosed.toBlowupClosed`, `SubstitutionClosed.toBlowupClosed` | [`BlowupClosed`](./BlowupClosed.lean), [`TrueClone`](./TrueClone.lean), [`Substitution`](./Substitution.lean) |
| §6 `thm:true-clone-root-plantable`, §7 `thm:substitution-root-plantable` | each a corollary of the unified theorem | `true_clone_root_plantable`, `substitution_root_plantable` | [`TrueClone`](./TrueClone.lean), [`Substitution`](./Substitution.lean) |
| (engine) | root-plantability from any uniform within-class blow-up closure | `subst_root_plantable` | [`SubstitutionClosed`](./SubstitutionClosed.lean) |
| §8 `def:finite-local-planting` | the finite planting property at `σ` | `FinitePlanting` | [`FinitePlanting`](./FinitePlanting.lean) |
| §8 `thm:finite-local-planting` | finite planting at a non-degenerate `σ` ⟹ root-plantable (`S_σ = Q_σ`) | `finitePlanting_root_plantable` | [`FinitePlanting`](./FinitePlanting.lean) |
| §8 `def:sparse-root-repair` | sparse root-blow-up repairs at `σ` | `SparseRootRepair` | [`SparseRootRepair`](./SparseRootRepair.lean) |
| §8 `thm:sparse-repair-planting` | sparse root repairs ⟹ finite planting | `sparseRootRepair_finitePlanting` | [`SparseRootRepair`](./SparseRootRepair.lean) |
| §8 `lem:c5-nbhd` | in a `C₅`-free graph, `e(G[N(v)]) ≤ |N(v)|` | `c5free_neighborhood_edge_card_le` (class `c5FreeClass`) | [`C5Free`](./C5Free.lean) |
| §8 `def:c5-one-root-planting` | the one-root planting `P_L(G,r)` | `oneRootPlant` | [`C5OneRoot`](./C5OneRoot.lean) |
| §8 `lem:c5-planting-free` | `P_L(G,r)` is `C₅`-free | `oneRootPlant_c5free` | [`C5OneRoot`](./C5OneRoot.lean) |
| §8 `lem:c5-one-root-sparse-repair`, `thm:c5-one-root` | the `C₅`-free class is root-plantable at the one-vertex type (`S₁ = Q₁`) | `c5FreeClass_sparseRootRepair_oneVertex`, `c5free_one_root_plantable` | [`C5OneRoot`](./C5OneRoot.lean) |
| §8 `def:c5-nonedge-planting`, `lem:c5-nonedge-planting-free` | two-root non-edge planting `P_L(G,r,s)` and its `C₅`-freeness | `twoRootPlant`, `twoRootPlant_c5free` | [`C5TwoRootNonEdge`](./C5TwoRootNonEdge.lean) |
| §8 `lem:c5-nonedge-sparse-repair`, `thm:c5-nonedge-root` | the `C₅`-free class is root-plantable at the two-root non-edge type (`S_η = Q_η`) | `c5FreeClass_sparseRootRepair_twoNonEdge`, `c5free_two_root_nonedge_plantable` | [`C5TwoRootNonEdge`](./C5TwoRootNonEdge.lean) |
| §8 `lem:c5-blowup` | an independent blow-up of a `C₅`-free graph is `C₅`-free iff triangle-free | `c5_blowup_free_iff_triangleFree` | [`C5Blowup`](./C5Blowup.lean) |
| §9 `thm:pinning` | almost-sure pinning plus a quotient point with a different value obstructs root-plantability | `pinning_obstruction` | [`Pinning`](./Pinning.lean) |
| §9 `def:edge-degenerate` | edge-degenerate / co-edge-degenerate classes; the one-root edge flag `e`, unlabelled edge `ρ`; endpoint a.s.-pinning | `EdgeDegenerate`, `CoEdgeDegenerate`, `e`, `ρ`, `ae_e_eq_zero_of_pinned`, `ae_e_eq_one_of_pinned` | [`EdgeObstruction`](./EdgeObstruction.lean) |
| §9 `thm:degenerate-obstruction` | edge-degenerate + arbitrarily large stars ⟹ not root-plantable at the one-vertex type | `degenerate_not_rootPlantable` | [`StarWitness`](./StarWitness.lean) |
| §9.1 `lem:c4-edge-zero` | the `C₄`-free class is edge-degenerate (elementary Kővári–Sós–Turán: `(2·e(G))² ≤ 2\|G\|³`) | `c4FreeClass_edgeDegenerate` (bound `c4free_card_edges_sq_le`) | [`C4Free`](./C4Free.lean) |
| §9.1 `cor:c4-counterexample` | `C₄`-free is not root-plantable at the one-vertex type | `c4free_not_rootPlantable` | [`C4Free`](./C4Free.lean) |
| §9.1 `cor:degenerate-family` | general principle: a subquadratic edge bound `e(G) ≤ f(\|G\|)`, `f N/N² → 0`, ⟹ edge-degenerate | `edgeDegenerate_of_subquadratic` | [`DegenerateFamily`](./DegenerateFamily.lean) |
| §9.2 `cor:codegenerate` | the *dense* complement-of-`C₄`-free class is also not root-plantable (density is not the dividing line) | `coDegenerate_not_rootPlantable`, `coC4free_not_rootPlantable` | [`StarWitness`](./StarWitness.lean), [`DenseObstruction`](./DenseObstruction.lean) |

A **new supporting theorem** that does not appear as a numbered result in the paper but is the
foundational input to `thm:clone-root-plantable`:

| | Statement | Lean name | Module |
|---|---|---|---|
| Constrained representation theorem | a positive hom vanishing on all forbidden flags is the density limit of a sequence of **forbidden-free** flags (a *constrained* refinement of Razborov 3.3(b)) | `exists_constrained_flagSeq_limit` | [`ConstrainedRep`](./ConstrainedRep.lean) |

§1 (Introduction) is prose and has nothing to formalise. **§6 (complete blow-ups / true twins)
and §7 (substitution-closed classes) are also formalised** (table above), reusing the §5 machinery
through the generalised blow-up `subBlowup`; **§8 (finite local planting and the `C₅`-free class) is
formalised too**, reusing the §5/§7 capstone toolkit (see the §8 rows above and Deviation 8).
**§9, §9.1 and §9.2 are formalised** (the abstract pinning obstruction `thm:pinning`, the degeneracy
obstruction `thm:degenerate-obstruction`, the `C₄`-free counterexample `lem:c4-edge-zero` /
`cor:c4-counterexample`, the general family criterion `cor:degenerate-family`, and the dense
counterpart `cor:codegenerate`), reusing the §5/§8 constrained-representation and class machinery.
The later §9 subsections (boundary/no-interior pinning, the `C₅`-edge obstruction) and the full
complementation *isomorphism* `lem:complementation` remain future work — see
[Scope & limitations](#scope--limitations).

A note on how to read the §8 rows against the paper, and what to scrutinise when checking the
correspondence by hand, is in [Auditing the correspondence to `paper.tex`](#auditing-the-correspondence-to-papertex) below.

---

## Status & verification

* **`sorry`-free.** No `sorry`/`admit`/`native_decide` appears in any module, and there are no
  `axiom` declarations.
* **Axiom-clean.** Every capstone theorem — the unified `blowupClosed_root_plantable`, the §5
  `clone_root_plantable` / `clique_free_root_plantable` / `clique_free_quotient_iff_ensemble`, the
  §6–§7 `true_clone_root_plantable` / `substitution_root_plantable` / `cluster_root_plantable`, and
  the §8 `finitePlanting_root_plantable` / `sparseRootRepair_finitePlanting` /
  `c5free_one_root_plantable` / `c5free_two_root_nonedge_plantable`, and the §9 `pinning_obstruction`
  / `degenerate_not_rootPlantable` / `c4free_not_rootPlantable` / `coDegenerate_not_rootPlantable` /
  `coC4free_not_rootPlantable` / `edgeDegenerate_of_subquadratic` — depends on **only the three
  standard Mathlib axioms** `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
* **Builds.** `lake build LeanFlagAlgebras.MetaTheory` compiles all 45 modules (7951 jobs); the full
  project `lake build LeanFlagAlgebras` builds with §9 integrated.
* **One non-default option.** Two §8 declarations carry `set_option maxHeartbeats …` (1000000 on
  `sparseRootRepair_finitePlanting`, 800000 on `c5FreeClass_sparseRootRepair_oneVertex`) — a raise of
  the elaboration step budget for proofs run in a large local context. This affects *how long* the
  kernel is willing to check, not *what* it checks: it is not `native_decide` and introduces no
  axiom; the `#print axioms` output above is unaffected.

### How to verify it yourself

```bash
# from the repository root
lake exe cache get                              # fetch the Mathlib cache (don't compile from source)
lake build LeanFlagAlgebras.MetaTheory          # build every MetaTheory module

# confirm there are no incomplete proofs
rg -n '\b(sorry|admit|native_decide)\b' LeanFlagAlgebras/MetaTheory -g '*.lean'   # → no output

# confirm the capstone depends only on the standard axioms (no sorryAx)
echo 'import LeanFlagAlgebras.MetaTheory.CloneClosed
open FlagAlgebras.MetaTheory
#print axioms clone_root_plantable' > /tmp/chk.lean
lake env lean /tmp/chk.lean
# → 'clone_root_plantable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Notable deviations from the paper

The formalisation is faithful to the paper's *statements and arguments*, with a few deliberate,
clearly-bounded changes. (Per-module detail is in [`ARCHITECTURE.md`](./ARCHITECTURE.md).)

1. **Uniform clone sizes in the planted estimate (a simplification).** The paper's
   `lem:planted-estimate` allows arbitrary clone sizes and pays a total-variation error term,
   giving an asymptotic bound `C_m(λ + 1/(n−k) + err_N)`. Our `planted_estimate` restricts to the
   **uniform non-root clone case**, which makes the clone-weighted sampling distribution *exactly*
   uniform and replaces the TV analysis with an **exact binomial good/bad count split**, yielding
   the clean bound `1 − ρ` with `ρ = M^{ℓ−k}·C(n−k,ℓ−k)/C(N−k,ℓ−k)`. This is the route actually
   taken by the capstone (`CloneClosed` drives `1 − ρ → 0` via the two limits in
   [`BinomialRatio`](./BinomialRatio.lean)). It is sufficient because
   `thm:clone-root-plantable` is free to *choose* the clone-size vector.
   *Consequence:* [`ProductTV`](./ProductTV.lean) — which correctly formalises the paper's
   general-clone TV bound `eq:good-unnormalized-weight-bound` — is **superseded and unused** on the
   critical path. It is retained (and marked as such in its header) as a correct, reusable lemma.

2. **The constrained representation theorem is a genuine strengthening.** The paper invokes "the
   representation theorem in the constrained class". Mathlib/this development only had the
   *unconstrained* representation theorem (`positiveHom_as_flagSeq_limit`). We therefore prove a
   new, stronger statement — [`exists_constrained_flagSeq_limit`](./ConstrainedRep.lean) — whose
   approximating flags are themselves **forbidden-free**, by intersecting the (full-measure)
   convergence event with a (full-measure) forbidden-free event under the same `flagSeqMeasure`.

3. **Weak convergence lives on `FlagDensitySpace σ`, not `PositiveHomSpace σ`.** A finite flag's
   density profile is *not* an honest positive homomorphism (it is only approximately
   multiplicative), so the per-term rooting measures cannot be pushed onto `X_σ = PositiveHomSpace σ`.
   [`WeakConvergence`](./WeakConvergence.lean) instead states convergence on the ambient compact
   space `FlagDensitySpace σ` to the inclusion-pushforward `(ℙ[φ₀]).map Subtype.val` — the honest
   object, still usable with a Portmanteau argument on `X_σ`.

4. **Minor generalisations / packaging.** `lem:support-as` is stated for any hereditarily-Lindelöf
   space (compact metric spaces qualify); `forbiddenIdeal_eq_span` concludes an equality of
   *carrier sets* (the ideal and the ℝ-span live in different `SetLike` types) and takes heredity
   as an explicit hypothesis; the hereditary clone-closed class is packaged as a reusable
   `GraphClass` structure ([`GraphClassConstraint`](./GraphClassConstraint.lean)). The
   `lem:planted-mass` count is over `ℚ`.

5. **§6–§7 are unified through one generalised blow-up** (matching the paper's revised §7, where
   `lem:general-planting-estimate` states the estimate for arbitrary interiors). We define a single
   construction `subBlowup G W` (the within-class family `W` is `⊤` for §6 and the in-class fibres
   for §7) and prove the estimate **once**: `planted_estimate_sub` is the §5 `planted_estimate`
   generalised to an arbitrary host (`planted_estimate_host`), since on the transversals the estimate
   samples, `subBlowup` is indistinguishable from the independent blow-up.
   Consequently the §6/§7 estimates inherit the uniform-clone simplification of Deviation 1 (the
   clean `1 − ρ`, with the same `ρ`), not the paper's general-clone `C_m(λ + 1/(n−k) + err_N)`.
   Likewise `subst_root_plantable` is `clone_root_plantable` re-run over `subBlowup` under an abstract
   *within-class blow-up closure* hypothesis, of which §6's `TrueCloneClosed` and §7's
   `SubstitutionClosed` are instances.

6. **§6–§7 packaging.** Heredity is separated from closure into a `HeredClass` structure
   ([`HeredClass`](./HeredClass.lean)), with the §5 `GraphClass extends HeredClass` adding
   `clone_closed` — because `cor:cluster-graphs` needs a class that is hereditary yet *not*
   clone-closed. The closure-agnostic constraint/consumption machinery and the construction-agnostic
   capstone toolkit ([`CapstoneShared`](./CapstoneShared.lean)) are therefore shared by §5, §6 and §7
   rather than duplicated. §7's "infinite" hypothesis is stated as its used consequence — the class
   contains a graph of every finite order (`∀ N, ∃ H : SimpleGraph (Fin N), hc.Mem H`). Cluster
   graphs are encoded by the equivalent `P₃`-free condition "adjacency is transitive on distinct
   vertices" rather than literally "disjoint union of cliques".

7. **`cor:cluster-graphs`: only the positive half is formalised.** We prove cluster graphs are
   root-plantable (`cluster_root_plantable`). The paper's accompanying remark that the class is *not*
   clone-closed (witnessed by `K₂`'s independent blow-up `K_{2,2} ⊇` induced `P₃`) is a separate
   finite construction we did not formalise; it is not needed for any theorem.

8. **§8 deviations.** The §8 *statements* are formalised faithfully; the deliberate changes are:
   * **(a) `thm:sparse-repair-planting` avoids the probabilistic coupling — a genuine simplification.**
     The paper proves the sampling estimate by *coupling* two without-replacement samples drawn from
     different ground sets (`|W| = N − k` for `H`, `|U| = n − k` for `G`) on one probability space.
     We instead prove a **purely combinatorial three-term bound** `counting_coupling_bound` (in
     [`SparseRootRepair`](./SparseRootRepair.lean)):
     `|p_H − p_G| ≤ 2·P_W[S⊄U] + P_W[S⊆U ∧ Bad]`, where the `C(N−k,q)` vs `C(n−k,q)` denominator
     mismatch (the very thing the coupling reconciles) is absorbed by elementary `Finset.card`
     algebra over `Finset.powersetCard`. No PMF/joint-distribution/measure-coupling machinery is
     introduced. The two bad-event bounds are binomial superset counts (the `C(|W|−1,q−1)`/
     `C(|W|−2,q−2)` ratios, via the same superset-count idiom as `PlantedEstimate`). The constant is
     `2mkλ + 4m²ρ` (a factor-2 looser on the first term than the paper's `2mkλ`), harmlessly absorbed
     since the theorem only needs *some* `λ, ρ` making the bound `< ε`.
   * **(b) "Non-degenerate type" is `0 < n₀`.** `thm:finite-local-planting` takes `hn₀ : 0 < n₀`. The
     two `C₅` instances are the one-vertex type `oneVertexType := (⊥ : SimpleGraph (Fin 1))` (`n₀ = 1`)
     and the two-root non-edge type `twoNonEdgeType := (⊥ : SimpleGraph (Fin 2))` (`n₀ = 2`).
   * **(c) Construction presentation.** `oneRootPlant`/`twoRootPlant` are built on the sum type
     `nonRoot G ⊕ (Fin k × Fin L)` (matching the paper's `U ⊔ R₁ ⊔ ⋯ ⊔ R_k`); since
     `FinitePlanting`'s conclusion asks for `H : SimpleGraph (Fin N)`,
     `sparseRootRepair_finitePlanting` transports the sum-type graph onto `Fin N` via
     `Fintype.equivFin` (`SimpleGraph.map`/`Iso.map`), and computes densities on the sum type via the
     iso-invariance `flagDensity₁_respect_eqv`. Clause (iii) of `def:sparse-root-repair` is encoded as
     a `Sym2`-symmetric-difference cardinality bound.
   * **(d) `twoRootPlant_c5free` is slightly more general than the paper lemma.** It is stated with
     the non-edge hypothesis `hrs : ¬ G.Adj r s` (to mirror `def:c5-nonedge-planting`), but the
     projection-based `C₅`-freeness proof does not use it; the non-edge property is supplied to the
     sparse-repair *instance* automatically from the type being `⊥`.

9. **§9 deviations.** The §9 / §9.1 / §9.2 *statements* are formalised faithfully; the deliberate
   choices are:
   * **(a) `cor:codegenerate` (Cor 51) is proved *without* `lem:complementation` (Lemma 50).** The
     paper proves Cor 51 by transferring `thm:degenerate-obstruction` for `K̄` back to `K` through the
     complementation isomorphism `lem:complementation`, and *separately* "identifies the witness
     directly". We take **only the direct-witness route**: `coDegenerate_not_rootPlantable` is built
     from the `c = 1` endpoint of `pinning_obstruction` (via `ae_e_eq_one_of_pinned`, i.e. a
     `[0,1]`-valued mean-`1` variable is a.s. `1`) plus a co-star quotient point with `ψ(e) = 0` — it
     contains **no graph-complement reasoning at all**. This matches the paper's own "Let us also
     identify the witness directly" argument and makes Cor 51 independent of Lemma 50.
   * **(b) `lem:complementation` (Lemma 50) is *not* formalised.** Its content — that the
     graph-complement map is an *algebra isomorphism* `A^σ[T] ≅ A^{σ̄}[T̄]` that transports `Q_σ`,
     `S_σ` and the random-extension measures, so root-plantability is a complementation invariant — is
     a large separate infrastructure effort (a complement endofunctor on the entire flag construction,
     plus precomposition/pushforward transfer of the whole semantic stack). It is left for future work.
     The *concrete* dense instance `coC4FreeClass` / `coC4free_not_rootPlantable` ([`DenseObstruction`](./DenseObstruction.lean))
     uses complementation only **elementarily** — the edge-count identity `e(G) + e(Gᶜ) = C(|G|,2)`
     (`card_edgeFinset_add_compl`, to reduce co-edge-degeneracy to the `C₄` bound on `Gᶜ`) and the
     graph equality `(coStarₙ)ᶜ = starₙ` — never the Lemma-50 isomorphism.
   * **(c) `cor:degenerate-family` (Cor 49): the general criterion, not all four families.** We
     formalise the common mechanism `edgeDegenerate_of_subquadratic` ([`DegenerateFamily`](./DegenerateFamily.lean)):
     a subquadratic edge bound `e(G) ≤ f(|G|)` with `f N / N² → 0` implies edge-degeneracy. Only the
     `C₄ = K_{2,2}` instance has its extremal bound proved from scratch (`c4free_card_edges_sq_le`);
     the other listed families — general `K_{s,t}` for `s ≥ 3` (Kővári–Sós–Turán), even cycles
     (Bondy–Simonovits), planar graphs (Euler) — instantiate the criterion via classical extremal
     bounds that are outside the current Mathlib, so they are stated at the level of the criterion
     rather than re-proved.
   * **(d) The `C₄` edge bound is an elementary cherry double-count, not the paper's convexity bound.**
     The paper bounds the average degree by `d̄ ≤ 1 + √N` (Jensen/convexity applied to
     `∑_v C(d(v),2) ≤ C(N,2)`). We instead prove the equivalent-strength `(2·e(G))² ≤ 2N³`
     (`c4free_card_edges_sq_le`) by double-counting cherries
     `∑_v d(v)(d(v)−1) = ∑_{x≠y} |N(x) ∩ N(y)| ≤ N(N−1)` (each pair has ≤ 1 common neighbour, else a
     `C₄`) followed by Cauchy–Schwarz, and then squeeze the **squared** density
     `(e(G)/C(N,2))² ≤ 2N/(N−1)² → 0` — working with the square avoids introducing `√`. Same
     conclusion (edge density → 0), a different elementary route.
   * **(e) The edge flag and `def:edge-degenerate`.** `EdgeDegenerate` is `φ₀(ρ) = 0` for all
     `φ₀ ∈ Q₀`, with `ρ := ⟦e⟧₀` and `e` the one-root edge over `vtype := (⊥ : FlagType (Fin 1))`. The
     unlabelling weight `downwardNormalizingFactor edgeFF.2 = 1` (`downwardNormalizingFactor_edge_eq_one`,
     proved via `isomorphismCount edgeLabeled = 2` — the edge `K₂` has two root placements, flag-iso
     via the `0↔1` swap) makes `φ₀(ρ)` the *genuine* unlabelled edge density, matching the paper's `ρ`
     and `⟨e⟩_v = ρ`. The "contains arbitrarily large stars" hypothesis (weakenable per the paper's
     remark) is encoded as `∀ N, ∃ n ≥ N, hc.Mem (starLabeled n).graph`.
   * **(f) `c4FreeClass` uses Mathlib `Free`/`IsContained`.** `Mem G := (cycleGraph 4).Free G` (no `C₄`
     as a not-necessarily-induced subgraph) — the same direct subgraph-containment encoding as §8's
     `c5FreeClass`, equal to the paper's `K_{C4}` (which it also describes in induced-flag language as
     forbidding the three four-vertex graphs containing a `C₄`).

None of these changes the theorems being proved; they are formalisation choices, and each is
documented in the relevant module's header.

---

## Auditing the correspondence to `paper.tex`

Because every proof is machine-checked and `sorry`-free, **a human audit reduces to checking that
each Lean *statement* faithfully encodes the corresponding paper claim** — the kernel guarantees the
rest. So the audit is *statement-level*: read the Lean `def`/`theorem` and compare it to the paper
`\begin{definition}`/`\begin{theorem}` it claims to formalise; you do **not** need to read the
proofs to trust the result, only to satisfy yourself that the hypotheses and conclusion match (and
that any deviation is one of the documented, harmless ones above).

**General orientation.** The notation map (`⟦·⟧`, `⟦·⟧₀`, `∅ₜ`, `⟨σ⟩₀`, `ℙ[φ₀]`, `≃f`, `↪g`,
`flagDensity₁`, `S_σ`, `Q_σ`, `RootPlantable`) is in [`READING_GUIDE.md`](./READING_GUIDE.md), which
also carries the full *paper-result → module → Lean-name* table for §2–§8. Every module opens with a
`/-! # … -/` header naming the `paper.tex` result(s) it formalises; start there. The semantic
objects (`Q_σ`, `S_σ`, `RootPlantable`, `Constraint`, the random extension `ℙ[φ₀]`) are defined in
[`ConstrainedClass`](./ConstrainedClass.lean) / [`SupportClosure`](./SupportClosure.lean) — read
those definitions once and the meaning of every "`S_σ = Q_σ`" conclusion is fixed.

**§8 audit map** (paper label @ `paper.tex` line ↦ Lean statement to read):

| `paper.tex` (line) | Lean statement to read | What to verify |
|---|---|---|
| `def:finite-local-planting` (l.2029) | `FinitePlanting` ([`FinitePlanting.lean`](./FinitePlanting.lean) l.56) | the three clauses (i) `|V H| ≥ |G|`, (ii) `|Θ| ≥ δ|V H|^k`, (iii) bounded-size density match — and the `∀ m,ε ∃ n₁,δ ∀ …` quantifier order |
| `thm:finite-local-planting` (l.2049) | `finitePlanting_root_plantable` (l.231) | conclusion is `RootPlantable (hc.constraintOf σ)` i.e. `S_σ = Q_σ`; non-degeneracy is `0 < n₀` |
| `def:sparse-root-repair` (l.2142) | `SparseRootRepair` ([`SparseRootRepair.lean`](./SparseRootRepair.lean) l.45) | the host vertex type `nonRoot G ⊕ (Fin n₀ × Fin L)` ≙ `U ⊔ R₁⊔⋯⊔R_k`; clauses (i)/(ii) cross-adjacency; clause (iii) `Sym2` symmetric-difference count `≤ ρn²`; `L ∈ [λn/2, λn]` |
| `thm:sparse-repair-planting` (l.2171) | `sparseRootRepair_finitePlanting` (l.807) | conclusion `FinitePlanting hc σ` (the proof's coupling-free route is Deviation 8a; the *statement* matches the paper) |
| `lem:c5-nbhd` (l.2330) | `c5free_neighborhood_edge_card_le` ([`C5Free.lean`](./C5Free.lean) l.357) | `(G.induce (G.neighborSet v)).edgeFinset.card ≤ Fintype.card (G.neighborSet v)` ≙ `e(G[N(v)]) ≤ |N(v)|`; and `c5FreeClass` (l.42) `Mem G := C5g.Free G` ≙ "no `C₅` subgraph" |
| `def:c5-one-root-planting` (l.2361) | `oneRootPlant` ([`C5OneRoot.lean`](./C5OneRoot.lean) l.31) | the `Adj` match: `R` independent, `R`–`U` join = `N(r)`, `U`-edges kept except inside `N(r)` |
| `lem:c5-planting-free` (l.2373) | `oneRootPlant_c5free` (l.78) | `C5g.Free (oneRootPlant G L)` from `C5g.Free G.graph` |
| `lem:c5-one-root-sparse-repair` (l.2404), `thm:c5-one-root` (l.2423) | `c5FreeClass_sparseRootRepair_oneVertex` (l.290), `c5free_one_root_plantable` (l.339) | the type is `oneVertexType = (⊥ : SimpleGraph (Fin 1))`; conclusion `RootPlantable (c5FreeClass.constraintOf oneVertexType)` ≙ `S₁ = Q₁` |
| `def:c5-nonedge-planting` (l.2456), `lem:c5-nonedge-planting-free` (l.2470) | `twoRootPlant` ([`C5TwoRootNonEdge.lean`](./C5TwoRootNonEdge.lean) l.31), `twoRootPlant_c5free` (l.160) | two clusters, no `R`–`S` edges, delete `U`-edges inside `N(r)` **or** `N(s)`; note Deviation 8d (`hrs`) |
| `lem:c5-nonedge-sparse-repair` (l.2504), `thm:c5-nonedge-root` (l.2527) | `c5FreeClass_sparseRootRepair_twoNonEdge` (l.319), `c5free_two_root_nonedge_plantable` (l.362) | the type is `twoNonEdgeType = (⊥ : SimpleGraph (Fin 2))` ≙ the non-edge type `η`; conclusion ≙ `S_η = Q_η` |
| `lem:c5-blowup` (l.2543) | `c5_blowup_free_iff_triangleFree` ([`C5Blowup.lean`](./C5Blowup.lean) l.29) | `(∀ m, C5g.Free (independentBlowup G m)) ↔ G.CliqueFree 3` |

**Statements worth the closest reading** (their Lean encoding involves a modelling choice you should
confirm is faithful, rather than a routine transcription): `FinitePlanting` and `SparseRootRepair`
(the quantifier structure and the sum-type host), and the planting `def`s `oneRootPlant`/`twoRootPlant`
(the `Adj` match arms). Everything else is a direct transcription. The documented deviations
(coupling-free counting, sum-type→`Fin N` presentation, `hrs`, the `maxHeartbeats` raises) are listed
in [Notable deviations](#notable-deviations-from-the-paper) Deviation 8.

**Mechanical re-verification** (reproduces the claims above, ~minutes after `lake exe cache get`):

```bash
lake build LeanFlagAlgebras.MetaTheory                                  # 7951 jobs, green
grep -rnwE 'sorry|admit|native_decide' LeanFlagAlgebras/MetaTheory --include='*.lean'   # → no output
printf 'import LeanFlagAlgebras.MetaTheory\nopen FlagAlgebras.MetaTheory\n%s\n' \
  '#print axioms finitePlanting_root_plantable
#print axioms sparseRootRepair_finitePlanting
#print axioms c5free_one_root_plantable
#print axioms c5free_two_root_nonedge_plantable
#print axioms degenerate_not_rootPlantable
#print axioms c4free_not_rootPlantable
#print axioms coC4free_not_rootPlantable
#print axioms edgeDegenerate_of_subquadratic' > /tmp/chk8.lean
lake env lean /tmp/chk8.lean        # each → [propext, Classical.choice, Quot.sound]
```

---

## How the existing flag-algebra formalisation enabled this

This meta-theory is a layer **on top of** the repository's existing formalisation of flag algebras
(`LeanFlagAlgebras/FlagAlgebra/`, `LeanFlagAlgebras/Forbid/`). That base supplied the entire
*semantic foundation* — Razborov's flag algebra, its homomorphism space, the random-extension
measure, the density and rooting machinery — so the §1–8 results could be **stated and proved by
reusing deep existing results rather than re-deriving the framework**. This is what reduced the task
from "formalise flag algebras *and then* the meta-theory" to "formalise the meta-theory, reusing
the flag algebras", and is the single biggest reason a `sorry`-free §1–8 was feasible. (§6–§7 add a
second layer of reuse on top — they are built by reusing §5, see the §6–§7 row of the results table
and Deviation 5 — and §8 a third, reusing the §5/§7 capstone toolkit, see item 9 below.) Concretely:

1. **The objects to talk about already existed.** `FlagAlgebra σ` (the algebra `A^σ`, with
   `basisVector`, the product, `flagDensity_self`), `PositiveHom σ`, and — crucially — the **compact
   metric homomorphism space `PositiveHomSpace σ` (`X_σ`)** with its `CompactSpace`/`MetricSpace`/
   closedness instances and coordinate continuity (`FinFlag.continuous`). Because `X_σ` and its
   topology were already in place, §2–§4 (`Q_σ`, `S_σ`, the support-closure criterion) could be
   phrased *directly* as topology/measure statements about `X_σ`, with no need to build the space.

2. **The representation theorem — and its proof *technique* — was reusable.**
   `positiveHom_as_flagSeq_limit` / `flagSeq_limit_mem_positiveHom` (FlagSequence) realise points of
   `X_σ` as graph limits. Its proof goes through a probabilistic construction — `flagSeqMeasure`,
   `randomDensity_expectation`, `flagSeqMeasure_error_prob_zero`. The **single hardest new result**,
   the constrained representation theorem (`ConstrainedRep`), was obtained by *adapting that very
   machinery*: intersecting the existing full-measure convergence event with a new full-measure
   "forbidden-free" event. Without the existing `flagSeqMeasure` development this step would have
   meant redeveloping the whole representation theorem from scratch.

3. **The random-extension measure `ℙ[φ₀]` gave the ensemble semantics for free.**
   `probMeasure_extend_emptyType_positiveHom` together with its **defining integral identity**
   (`…_spec`: `∫ φ f dℙ[φ₀] = φ₀⟦f⟧₀ / φ₀⟨σ⟩₀`, Razborov 3.5) is what "ensemble non-negativity" and
   the §3 *support-passes* lemma are manipulations of. The surrounding tightness/weak-convergence
   results — `flagDensitySpace_probMeasure_isSeqCompact` (Prokhorov),
   `exists_converge_flagSeq_and_probMeasure_tendsto`,
   `tendsto_integral_flagDensitySpace_of_converge_flagSeq`,
   `increasing_flagSeq_contain_convergent_subseq` — reduced `WeakConvergence`'s hard
   "`P_M ⇒ ℙ[φ₀]`" theorem to a subsequence-uniqueness argument over existing lemmas, instead of
   from-scratch measure theory.

4. **The rooting measure and its combinatorics collapsed the capstone's crux.** `FinFlag.toPMF` /
   `FinFlag.toProbMeasure` (the σ-rooting probability measure, weighted by
   `downwardNormalizingFactor`) and the count identities `isomorphismCount`, `labelExtensions`, and
   `isoInjectiveMapSet_card_eq_sum_labelExtensions_isomorphismCount_mul_labeledGraphCount` (all in
   FlagOperators) were exactly what `RootingUniform` and the crux `planted_cylinder_mass` needed:
   because `isomorphismCount` *already* counts σ-rootings per isomorphism class, the feared
   measure-↔-embedding bridge became a short regrouping rather than a several-hundred-line
   development.

5. **Flag density as a count, and the labelled-graph machinery, underpin the whole planted
   estimate.** `flagDensity₁`, `flagDensity_self` (a flag has density `1` in itself — the
   *self-forbidding* trick), `labeledGraphCount`, `subflagDensity`, and
   `LabeledGraph` / `LabeledSubgraph` / `inducedLabeledSubgraph` / `≃f` (`LabeledGraphIso`) from
   `FlagDef` drive `DensityBridge`, `LabeledCount`, `CloneCount`/`CloneTotal`/`PlantedCount`,
   `PlantedEstimate`, and the heredity lemmas in `GraphClassConstraint`.

6. **The labelled/unlabelled bridge was already built.** The `downward` operators (`⟦·⟧₀`),
   `⟨σ⟩₀` (`flagType_asEmptyTypeAlgebra`), and `downwardNormalizingFactor` are the translation
   between the σ-labelled and `∅ₜ`-unlabelled (graph) worlds that §3 and §5 cross constantly.

7. **The single-forbidden-flag pattern was the template to generalise.** `Forbid/Basic`'s
   `forbidEq` / `forbidLE` (reasoning conditioned a.s. on one forbidden flag) is conceptually what
   the `Constraint` / `GraphClass` framework here generalises to an entire forbidden family.

8. **Mathlib provided the analytic finale on top of the repo base:** Stone–Weierstrass and Urysohn
   (the support-closure criterion), closed-set Portmanteau and `Measure.support` (the capstone's
   limit step), `Ideal.Quotient` (the §3 quotient algebra), and `SimpleGraph.CliqueFree.comap`
   (`K_r`-free heredity).

9. **§8 reused the §5/§7 *meta-theory* layer, almost verbatim.** `thm:finite-local-planting` is
   structurally the §5 capstone `clone_root_plantable` with the blow-up sequence replaced by the
   abstract planting family `Hₜ`. It reuses **the construction-agnostic capstone toolkit
   [`CapstoneShared`](./CapstoneShared.lean)** exactly as that module's header anticipated ("reusable
   for §8+"): `mem_closure_of_forall_finset_cylinder` (reduce `ψ ∈ S_σ` to finite cylinders),
   `cyl`/`isClosed_cyl` (the closed set for Portmanteau), `flagDensity₁_respect_eqv`, and crucially
   `toProbMeasure_apply_eq_labeling_ratio` + `card_labelings_eq_card_embeddings` (which turn the
   planting's `|Θ| ≥ δ|V|^k` directly into `P_t(C̃) ≥ δ`). It reuses **`tendsto_rootingMeasure_extend`**
   ([`WeakConvergence`](./WeakConvergence.lean)) unchanged — that lemma was already proved for *any*
   convergent flag sequence, so the §8 family `Hₜ` (not a blow-up) feeds it directly — and the §4
   support/Portmanteau tail (`Sσ_subset_Qσ`, `mem_Qσ_iff`, `Measure.support`,
   `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`), the constrained representation
   `exists_constrained_flagSeq_limit`, the subsequence-limit lemmas
   (`increasing_flagSeq_contain_convergent_subseq`, `flagSeq_limit_mem_positiveHom`), and
   `subgraphDensity`/`subgraphCount` (for the uniform `σ`-type-density lower bound). The `C₅`-free
   class is a one-line [`HeredClass`](./HeredClass.lean) instance over Mathlib's
   `SimpleGraph.IsContained`/`Free`/`Copy` and `cycleGraph`, and `lem:c5-nbhd` is pure Mathlib graph
   theory (`induce`, `edgeFinset`, walks/paths, `IsTree.card_edgeFinset`, `girth`). `lem:c5-blowup`
   reuses §5's `independentBlowup`.

What is genuinely **new** here — not present in the existing formalisation — is the meta-theory
layer itself: the constrained class and quotient (§3), the support-closure criterion (§4), the
independent blow-up with its planted estimate and the reusable `GraphClass` packaging, the capstone
(§5), the constrained representation theorem, and — for §8 — the finite-planting criterion, the
coupling-free sparse-repair counting bound, and the `C₅`-free planting constructions. These are built
*with*, but go beyond, the flag-algebra base.

---

## Repository layout (this directory)

* **`paper.tex`** — the source article; §1–8 and §9's abstract pinning obstruction are formalised here.
* **`*.lean`** — 45 modules (see [`ARCHITECTURE.md`](./ARCHITECTURE.md) for the full map). They are
  imported and re-exported by [`../MetaTheory.lean`](../MetaTheory.lean), the aggregator, which in
  turn is in the top-level build manifest `../../LeanFlagAlgebras.lean`.
* **`README.md`** (this file), **`ARCHITECTURE.md`**, **`READING_GUIDE.md`** — documentation.

This `MetaTheory` development is built *on top of* the main `LeanFlagAlgebras/` formalisation of
flag algebras and adds new theory rather than re-deriving that machinery — see
[How the existing flag-algebra formalisation enabled this](#how-the-existing-flag-algebra-formalisation-enabled-this)
above, and the repository's top-level `CLAUDE.md` for the overall flag-algebra codebase.

---

## Scope & limitations

* **Formalised:** the proved results of §1–8 (above) — including §6 (complete blow-ups / true twins,
  `thm:true-clone-root-plantable`, `cor:cluster-graphs`), §7 (substitution-closed classes,
  `thm:substitution-root-plantable`), obtained by generalising the §5 planted estimate to the
  generalised blow-up `subBlowup` (`SubstitutionBlowup`/`SubstitutionEstimate`/`SubstitutionClosed`),
  and §8 (the finite-local-planting criterion `thm:finite-local-planting`, `thm:sparse-repair-planting`,
  and the `C₅`-free root-plantability results `thm:c5-one-root`/`thm:c5-nonedge-root` with `lem:c5-nbhd`
  and `lem:c5-blowup`) in the `FinitePlanting`/`SparseRootRepair`/`C5Free`/`C5OneRoot`/
  `C5TwoRootNonEdge`/`C5Blowup` modules, plus §9's abstract pinning obstruction
  (`thm:pinning`) in `Pinning`, and **§9 / §9.1 / §9.2** — the degeneracy obstruction
  (`thm:degenerate-obstruction`), the `C₄`-free counterexample (`lem:c4-edge-zero`,
  `cor:c4-counterexample`), the general family criterion (`cor:degenerate-family`), and the dense
  complement obstruction (`cor:codegenerate`) — in `EdgeObstruction`/`StarWitness`/`C4Free`/
  `DegenerateFamily`/`DenseObstruction`.
* **Not formalised (future work):** the later §9 results of `paper.tex` — the full complementation
  *isomorphism* `lem:complementation` (only its elementary edge-count consequence is used here; the
  algebra-iso + `Q_σ`/`S_σ`/measure-pushforward transfer is a large separate infrastructure effort),
  the general pinning *conjecture* (`conj:characterisation`), the boundary/no-interior theorems
  (`thm:no-interior`, `subsec:boundary`), the `C₅`-edge obstruction (`sec:c5-edge`,
  `thm:c5-edge-not-root-plantable`), the §10 `prop:empty-type` and later consequences. The criterion
  and machinery here are intended to be reusable for those. The four families of
  `cor:degenerate-family` other than `C₄` (general `K_{s,t}` with `s ≥ 3`, even cycles, planar)
  instantiate `edgeDegenerate_of_subquadratic` via classical extremal bounds that are outside the
  current Mathlib, so only the criterion (not those specific instances) is formalised.
* The development reuses results from the surrounding `LeanFlagAlgebras/FlagAlgebra/` directory
  (representation theorem, random-extension measure, Prokhorov compactness, …) as already-proved
  lemmas — these are part of the trusted base, not re-verified here, but they are themselves
  `sorry`-free Lean proofs, not axioms.
