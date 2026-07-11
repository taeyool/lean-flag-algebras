import LeanFlagAlgebras.MetaTheory.ParametricP4Slice
import LeanFlagAlgebras.MetaTheory.GraphonHom

/-! # The `ω_Zyk` route of parametric quantitative stability (Thm 112(iv))

`thm:parametric-quant-stability` part (iv) of `paper.tex`: near-extremal `P₄` density pins
the graphon near the balanced complete `r`-partite graphon **through the `K₄` density and a
Zykov stability modulus**.  The paper's proof is a one-line composition: clause (ii) — the
near-extremal `K₄`-density bound `parametricP4_K4_density_approx` — feeds the assumed
modulus.

As in `GraphonQuantStability.stability_via_modulus` (the `r = 3` / `ω_Tur` route of
Thm 111), the modulus and its cut-distance conclusion are abstracted: the target
`close : Prop` stands for `δ_□(W, T_r) < γ`, and the modulus enters as the named hypothesis
`hmod` (its existence is classical — by compactness and the assumed equality case — and is
exactly the `ω_Zyk` external input of the paper; no cut-distance machinery is built here,
matching the paper's own treatment of `ω_Tur`).

* `parametric_stability_via_modulus` — the hom-level Thm 112(iv): if the certificate
  deficit satisfies `Δ ≤ p₀(r)·ω`, and `K₄`-density within `ω` of extremal implies `close`,
  then `close`.
* `parametric_graphon_stability_via_modulus` — the same statement instantiated at
  `φ₀ := graphonHom W`, the paper's graphon-facing reading.

Tier-2 (consumes `parametricP4_K4_density_approx`, which carries the certificate axioms).
Notably, the Zykov *bound* hypothesis is not needed here at all: the `K₄`-density
approximation drops the certificate's Zykov term without using its sign, so the only
classical content of the theorem is the modulus `hmod` itself — formally, these theorems
are hypothesis-free beyond `hmod` and slice consistency. -/

open scoped Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras
open CompleteGraphFreeP4

/-- Strict positivity of `p₀` for `r ≥ 3`, re-derived here since the corresponding lemma
in `ParametricP4Slice` is private. -/
private lemma p₀_pos' (r : ℕ) (hr : 3 ≤ r) : 0 < p₀ r := by
  have hx : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD := denom_factor_pos r hr
  unfold p₀
  apply div_pos
  · nlinarith
  · linarith

variable {r : ℕ} (hr : 3 ≤ r)

include hr in
/-- **Thm 112(iv), hom level** (`thm:parametric-quant-stability`, clause `pq:zykov`): let
`ω` be a Zykov stability modulus value — `K₄` density within `ω` of the extremal value
implies the target property `close` (classically, `δ_□(·, T_r) < γ`).  If the certificate
deficit satisfies `Δ = 12((r−1)/r)³ − φ₀(π_{P₄}) ≤ p₀(r)·ω`, then `close` holds.

Proof route: `parametricP4_K4_density_approx` gives
`φ₀(K₄) ≥ extremal − Δ/p₀(r) ≥ extremal − ω` (using `p₀ r > 0`, re-derive the private
positivity of `ParametricP4Slice`); apply `hmod`. -/
theorem parametric_stability_via_modulus (φ₀ : PositiveHom ∅ₜ)
    (hQ : posHomPoint φ₀ ∈ Qσ (krFreeForb0 r))
    {ω : ℝ} {close : Prop}
    (hmod : ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / (r : ℝ) ^ 3 - ω
        ≤ φ₀ FlagAlgebra_4_0_0_10 → close)
    (hsmall : 12 * (((r : ℝ) - 1) / r) ^ 3 - φ₀ CompleteGraphFreeP4.P4_density
        ≤ p₀ r * ω) :
    close := by
  have hK4 := parametricP4_K4_density_approx hr φ₀ hQ
  have hp₀ := p₀_pos' r hr
  have hdiv : (12 * (((r : ℝ) - 1) / r) ^ 3 - φ₀ CompleteGraphFreeP4.P4_density) / p₀ r
      ≤ ω := (div_le_iff₀ hp₀).mpr (by linarith)
  apply hmod
  linarith

include hr in
/-- **Thm 112(iv) at a graphon** — the paper's graphon-facing form, instantiating
`parametric_stability_via_modulus` at `φ₀ := graphonHom W`. -/
theorem parametric_graphon_stability_via_modulus (W : Graphon)
    (hQ : posHomPoint (graphonHom W) ∈ Qσ (krFreeForb0 r))
    {ω : ℝ} {close : Prop}
    (hmod : ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / (r : ℝ) ^ 3 - ω
        ≤ (graphonHom W) FlagAlgebra_4_0_0_10 → close)
    (hsmall : 12 * (((r : ℝ) - 1) / r) ^ 3
        - (graphonHom W) CompleteGraphFreeP4.P4_density ≤ p₀ r * ω) :
    close :=
  parametric_stability_via_modulus hr (graphonHom W) hQ hmod hsmall

end FlagAlgebras.MetaTheory
