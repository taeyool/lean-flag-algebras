# MetaTheory — a Lean 4 formalisation of the root-plantability meta-theory of flag algebras

This directory formalises, in Lean 4 (toolchain `leanprover/lean4:v4.27.0`, Mathlib `v4.27.0`),
the **proved results of Sections 1–7 of [`paper.tex`](./paper.tex)** — the *meta-theory* of
flag algebras that asks **when forbidden-subgraph ("quotient") reasoning is complete** for a
constrained graph class.

The headline result is:

> **`clone_root_plantable`** ([`CloneClosed.lean`](./CloneClosed.lean)) — every clone-closed
> hereditary graph class is *root-plantable*: for a non-degenerate type `σ`, the supported space
> `S_σ` equals the quotient space `Q_σ`. Consequently quotient semantics and ensemble semantics
> agree for **every** `f ∈ A^σ`. Specialised to `K_r`-free graphs, this is **`cor:clique-free`**
> (`clique_free_root_plantable` / `clique_free_quotient_iff_ensemble`), covering the
> triangle-free case `r = 3`.

The same conclusion is then extended (§6–§7) to classes closed under **complete blow-ups**
(true twins) — **`true_clone_root_plantable`**, with `cluster_root_plantable` covering cluster
graphs, which are *not* clone-closed — and under **substitution** —
**`substitution_root_plantable`**. All three are instances of one generalised theorem
**`subst_root_plantable`** ([`SubstitutionClosed.lean`](./SubstitutionClosed.lean)), obtained by
reusing the §5 proof over a *generalised blow-up* `subBlowup`.

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
| §6/§7 `lem:true-planted-estimate`, `lem:substitution-planting-estimate` | the planted mass + estimate carry over to the generalised blow-up | `planted_mass_sub`, `planted_estimate_sub` | [`SubstitutionEstimate`](./SubstitutionEstimate.lean) |
| §6 `thm:true-clone-root-plantable` | true-clone-closed hereditary classes are root-plantable | `true_clone_root_plantable`, `true_clone_quotient_iff_ensemble` | [`TrueClone`](./TrueClone.lean) |
| §6 `cor:cluster-graphs` | cluster graphs (`P₃`-free; not clone-closed) are root-plantable | `cluster_root_plantable`, `cluster_quotient_iff_ensemble` | [`ClusterGraph`](./ClusterGraph.lean) |
| §7 `def:graph-substitution` | the substitution `G[H_v]` (= `subBlowup G H`) | `subBlowup` | [`SubstitutionBlowup`](./SubstitutionBlowup.lean) |
| §7 `thm:substitution-root-plantable` | infinite substitution-closed hereditary classes are root-plantable | `substitution_root_plantable`, `substitution_quotient_iff_ensemble` | [`Substitution`](./Substitution.lean) |
| (shared) | root-plantability from any within-class blow-up closure | `subst_root_plantable` | [`SubstitutionClosed`](./SubstitutionClosed.lean) |

A **new supporting theorem** that does not appear as a numbered result in the paper but is the
foundational input to `thm:clone-root-plantable`:

| | Statement | Lean name | Module |
|---|---|---|---|
| Constrained representation theorem | a positive hom vanishing on all forbidden flags is the density limit of a sequence of **forbidden-free** flags (a *constrained* refinement of Razborov 3.3(b)) | `exists_constrained_flagSeq_limit` | [`ConstrainedRep`](./ConstrainedRep.lean) |

§1 (Introduction) is prose and has nothing to formalise. **§6 (complete blow-ups / true twins)
and §7 (substitution-closed classes) are also formalised** (table above), reusing the §5 machinery
through the generalised blow-up `subBlowup`. Sections **§8 onward** of `paper.tex` (finite local
planting, degeneracy obstructions, …) are **out of scope** here — see
[Scope & limitations](#scope--limitations).

---

## Status & verification

* **`sorry`-free.** No `sorry`/`admit`/`native_decide` appears in any module, and there are no
  `axiom` declarations.
* **Axiom-clean.** Every capstone theorem — the §5 `clone_root_plantable` /
  `clique_free_root_plantable` / `clique_free_quotient_iff_ensemble` and the §6–§7
  `subst_root_plantable` / `true_clone_root_plantable` / `substitution_root_plantable` /
  `cluster_root_plantable` — depends on **only the three standard Mathlib axioms**
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
* **Builds.** `lake build LeanFlagAlgebras.MetaTheory` compiles all 31 modules (7937 jobs).

### How to verify it yourself

```bash
# from the repository root
lake exe cache get                              # fetch the Mathlib cache (don't compile from source)
lake build LeanFlagAlgebras.MetaTheory          # build every MetaTheory module

# confirm there are no incomplete proofs
grep -rnE 'sorry|admit|native_decide' LeanFlagAlgebras/MetaTheory --include='*.lean'   # → no output

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

5. **§6–§7 are unified through one generalised blow-up.** The paper proves `lem:true-planted-estimate`
   and `lem:substitution-planting-estimate` separately (complete blow-ups vs. substitution). We
   define a single construction `subBlowup G W` (the within-class family `W` is `⊤` for §6 and the
   in-class fibres for §7) and prove the estimate **once**: `planted_estimate_sub` is the §5
   `planted_estimate` generalised to an arbitrary host (`planted_estimate_host`), since on the
   transversals the estimate samples, `subBlowup` is indistinguishable from the independent blow-up.
   Consequently the §6/§7 estimates inherit the uniform-clone simplification of Deviation 1 (the
   clean `1 − ρ`, with the same `ρ`), not the paper's general-clone `C_m(λ + 1/(n−k) + err_N)`.
   Likewise `subst_root_plantable` is `clone_root_plantable` re-run over `subBlowup` under an abstract
   *within-class blow-up closure* hypothesis, of which §6's `TrueCloneClosed` and §7's
   `SubstitutionClosed` are instances.

6. **§6–§7 packaging.** Heredity is separated from closure into a `HeredClass` structure (the §5
   `GraphClass` bundled `clone_closed`, but `cor:cluster-graphs` needs a class that is hereditary yet
   *not* clone-closed). §7's "infinite" hypothesis is stated as its used consequence — the class
   contains a graph of every finite order (`∀ N, ∃ H : SimpleGraph (Fin N), hc.Mem H`). Cluster
   graphs are encoded by the equivalent `P₃`-free condition "adjacency is transitive on distinct
   vertices" rather than literally "disjoint union of cliques".

7. **`cor:cluster-graphs`: only the positive half is formalised.** We prove cluster graphs are
   root-plantable (`cluster_root_plantable`). The paper's accompanying remark that the class is *not*
   clone-closed (witnessed by `K₂`'s independent blow-up `K_{2,2} ⊇` induced `P₃`) is a separate
   finite construction we did not formalise; it is not needed for any theorem.

None of these changes the theorems being proved; they are formalisation choices, and each is
documented in the relevant module's header.

---

## How the existing flag-algebra formalisation enabled this

This meta-theory is a layer **on top of** the repository's existing formalisation of flag algebras
(`LeanFlagAlgebras/FlagAlgebra/`, `LeanFlagAlgebras/Forbid/`). That base supplied the entire
*semantic foundation* — Razborov's flag algebra, its homomorphism space, the random-extension
measure, the density and rooting machinery — so the §1–7 results could be **stated and proved by
reusing deep existing results rather than re-deriving the framework**. This is what reduced the task
from "formalise flag algebras *and then* the meta-theory" to "formalise the meta-theory, reusing
the flag algebras", and is the single biggest reason a `sorry`-free §1–7 was feasible. (§6–§7 add a
second layer of reuse on top: they are built by reusing §5 — see the §6–§7 row of the results table
and Deviation 5.) Concretely:

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

What is genuinely **new** here — not present in the existing formalisation — is the meta-theory
layer itself: the constrained class and quotient (§3), the support-closure criterion (§4), the
independent blow-up with its planted estimate and the reusable `GraphClass` packaging, the capstone
(§5), and the constrained representation theorem. These are built *with*, but go beyond, the
flag-algebra base.

---

## Repository layout (this directory)

* **`paper.tex`** — the source article; §1–7 are what is formalised here.
* **`*.lean`** — 31 modules (see [`ARCHITECTURE.md`](./ARCHITECTURE.md) for the full map). They are
  imported and re-exported by [`../MetaTheory.lean`](../MetaTheory.lean), the aggregator, which in
  turn is in the top-level build manifest `../../LeanFlagAlgebras.lean`.
* **`README.md`** (this file), **`ARCHITECTURE.md`**, **`READING_GUIDE.md`** — documentation.

This `MetaTheory` development is built *on top of* the main `LeanFlagAlgebras/` formalisation of
flag algebras and adds new theory rather than re-deriving that machinery — see
[How the existing flag-algebra formalisation enabled this](#how-the-existing-flag-algebra-formalisation-enabled-this)
above, and the repository's top-level `CLAUDE.md` for the overall flag-algebra codebase.

---

## Scope & limitations

* **Formalised:** the proved results of §1–7 (above) — including §6 (complete blow-ups / true twins,
  `thm:true-clone-root-plantable`, `cor:cluster-graphs`) and §7 (substitution-closed classes,
  `thm:substitution-root-plantable`), obtained by generalising the §5 planted estimate to the
  generalised blow-up `subBlowup` (`SubstitutionBlowup`/`SubstitutionEstimate`/`SubstitutionClosed`).
* **Not formalised (future work):** §8 onward of `paper.tex` — the finite-local-planting criterion,
  and the degeneracy obstructions (`thm:degenerate-obstruction`, the pinning theorems, …). The
  generalised-blow-up machinery here is intended to be reusable for those.
* The development reuses results from the surrounding `LeanFlagAlgebras/FlagAlgebra/` directory
  (representation theorem, random-extension measure, Prokhorov compactness, …) as already-proved
  lemmas — these are part of the trusted base, not re-verified here, but they are themselves
  `sorry`-free Lean proofs, not axioms.
