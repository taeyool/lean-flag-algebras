import LeanFlagAlgebras.MetaTheory.MeasureSupport
import LeanFlagAlgebras.MetaTheory.EvalAlgebra
import LeanFlagAlgebras.MetaTheory.ConstrainedClass
import LeanFlagAlgebras.MetaTheory.SupportClosure
import LeanFlagAlgebras.MetaTheory.Blowup

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
  projection, and the preservation of `K_r`-freeness (the core of `cor:clique-free`).

Still to come (§5): the quantitative estimates `lem:planted-mass` and `lem:planted-estimate`
(in `Blowup`), and `CloneClosed` (clone-closed classes are root-plantable; clique-free and
triangle-free corollary), plus
the §3 faithfulness lemma `forbiddenIdeal_eq_span` (heredity ⟹ the forbidden flags span an
ideal).
-/
