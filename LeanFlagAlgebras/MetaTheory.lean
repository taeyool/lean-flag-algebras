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
import LeanFlagAlgebras.MetaTheory.GraphClassConstraint
import LeanFlagAlgebras.MetaTheory.BinomialRatio
import LeanFlagAlgebras.MetaTheory.WeakConvergence

/-! # Meta-theory of flag algebras (`MetaTheory/paper.tex`)

Formalisation of the proved results in §1–5 of `MetaTheory/paper.tex`: when forbidden-subgraph
("quotient") reasoning is *complete* for a constrained graph class.

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
* `GraphClassConstraint` — the hereditary clone-closed `GraphClass` (`Mem`/`comap`/`clone_closed`),
  its `Constraint` (`constraintOf`), the two capstone-consumption lemmas `mem_of_forbiddenFree`
  (forbidden-free ⟹ in class, via `flagDensity_self`) and `forbiddenFree_of_mem` (in class ⟹
  forbidden-free, via the containment bridge + `comap`), and the `K_r`-free instance
  `cliqueFreeClass`.

* `BinomialRatio`    — the analytic core of the planted limit under uniform clone sizes:
  `rho_tendsto_atTop` (`M^(ℓ−k)·C(n−k,ℓ−k)/C(nM−k,ℓ−k) → descFactorial(n−k,ℓ−k)/n^(ℓ−k)` as
  `M→∞`) and `rho_inf_tendsto_one` (that limit `→ 1` as `n→∞`).
* `WeakConvergence`  — `tendsto_rootingMeasure_extend`: the σ-rooting measures of *any* flag
  sequence converging to `φ₀` converge weakly (on `FlagDensitySpace σ`) to the inclusion-
  pushforward `(ℙ[φ₀]).map Subtype.val` of the random extension (subsequence-uniqueness via the
  existing integral identification + `measure_eq_of_integral_flag_eq`).

Still to come (§5): `thm:clone-root-plantable` (assemble the constrained representation, the
uniform blow-up sequence, `WeakConvergence` + closed-set Portmanteau, and the `BinomialRatio`/
`planted_estimate`/`lem:planted-mass` quantitative bounds) and `cor:clique-free` (from
`cliqueFreeClass`).
-/
