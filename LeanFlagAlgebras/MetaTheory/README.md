# MetaTheory — a Lean 4 formalisation of the root-plantability meta-theory of flag algebras

This directory formalises, in Lean 4 (toolchain `leanprover/lean4:v4.27.0`, Mathlib `v4.27.0`),
the **proved results of Sections 1–5 of [`paper.tex`](./paper.tex)** — the *meta-theory* of
flag algebras that asks **when forbidden-subgraph ("quotient") reasoning is complete** for a
constrained graph class.

The headline result is:

> **`clone_root_plantable`** ([`CloneClosed.lean`](./CloneClosed.lean)) — every clone-closed
> hereditary graph class is *root-plantable*: for a non-degenerate type `σ`, the supported space
> `S_σ` equals the quotient space `Q_σ`. Consequently quotient semantics and ensemble semantics
> agree for **every** `f ∈ A^σ`. Specialised to `K_r`-free graphs, this is **`cor:clique-free`**
> (`clique_free_root_plantable` / `clique_free_quotient_iff_ensemble`), covering the
> triangle-free case `r = 3`.

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

A **new supporting theorem** that does not appear as a numbered result in the paper but is the
foundational input to `thm:clone-root-plantable`:

| | Statement | Lean name | Module |
|---|---|---|---|
| Constrained representation theorem | a positive hom vanishing on all forbidden flags is the density limit of a sequence of **forbidden-free** flags (a *constrained* refinement of Razborov 3.3(b)) | `exists_constrained_flagSeq_limit` | [`ConstrainedRep`](./ConstrainedRep.lean) |

§1 (Introduction) is prose and has nothing to formalise. Sections **§6 onward** of `paper.tex`
(true twins / complete blow-ups, substitution-closed classes, finite local planting, degeneracy
obstructions, …) are **out of scope** here — see [Scope & limitations](#scope--limitations).

---

## Status & verification

* **`sorry`-free.** No `sorry`/`admit`/`native_decide` appears in any module, and there are no
  `axiom` declarations.
* **Axiom-clean.** The three capstone theorems (`clone_root_plantable`,
  `clique_free_root_plantable`, `clique_free_quotient_iff_ensemble`) depend on **only the three
  standard Mathlib axioms** `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
* **Builds.** `lake build LeanFlagAlgebras.MetaTheory` compiles all 23 modules (≈7900 jobs).

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

None of these changes the theorems being proved; they are formalisation choices, and each is
documented in the relevant module's header.

---

## How the existing flag-algebra formalisation enabled this

This meta-theory is a layer **on top of** the repository's existing formalisation of flag algebras
(`LeanFlagAlgebras/FlagAlgebra/`, `LeanFlagAlgebras/Forbid/`). That base supplied the entire
*semantic foundation* — Razborov's flag algebra, its homomorphism space, the random-extension
measure, the density and rooting machinery — so the §1–5 results could be **stated and proved by
reusing deep existing results rather than re-deriving the framework**. This is what reduced the task
from "formalise flag algebras *and then* the meta-theory" to "formalise the meta-theory, reusing
the flag algebras", and is the single biggest reason a `sorry`-free §1–5 was feasible. Concretely:

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

* **`paper.tex`** — the source article; §1–5 are what is formalised here.
* **`*.lean`** — 23 modules (see [`ARCHITECTURE.md`](./ARCHITECTURE.md) for the full map). They are
  imported and re-exported by [`../MetaTheory.lean`](../MetaTheory.lean), the aggregator, which in
  turn is in the top-level build manifest `../../LeanFlagAlgebras.lean`.
* **`README.md`** (this file), **`ARCHITECTURE.md`**, **`READING_GUIDE.md`** — documentation.

This `MetaTheory` development is built *on top of* the main `LeanFlagAlgebras/` formalisation of
flag algebras and adds new theory rather than re-deriving that machinery — see
[How the existing flag-algebra formalisation enabled this](#how-the-existing-flag-algebra-formalisation-enabled-this)
above, and the repository's top-level `CLAUDE.md` for the overall flag-algebra codebase.

---

## Scope & limitations

* **Formalised:** the proved results of §1–5 (above).
* **Not formalised (future work):** §6+ of `paper.tex` — complete blow-ups / true twins
  (`thm:true-clone-root-plantable`), substitution-closed classes
  (`thm:substitution-root-plantable`), the finite-local-planting criterion, and the degeneracy
  obstructions (`thm:degenerate-obstruction`, the pinning theorems, …). The §5 machinery here
  (especially the planted estimate and the `GraphClass` packaging) is intended to be reusable for
  those.
* The development reuses results from the surrounding `LeanFlagAlgebras/FlagAlgebra/` directory
  (representation theorem, random-extension measure, Prokhorov compactness, …) as already-proved
  lemmas — these are part of the trusted base, not re-verified here, but they are themselves
  `sorry`-free Lean proofs, not axioms.
