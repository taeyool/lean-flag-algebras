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

Still to come (§5): `lem:planted-estimate` (the sampling argument gluing the subset count to
`ProductTV` via `blowupGoodIso` and bad-event bounds), then `thm:clone-root-plantable`
(representation theorem + Portmanteau + `MeasureUniqueness`) and `CloneClosed` (clone-closed classes are root-plantable; clique-free and
triangle-free corollary), plus
the §3 faithfulness lemma `forbiddenIdeal_eq_span` (heredity ⟹ the forbidden flags span an
ideal).
-/
