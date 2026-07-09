import LeanFlagAlgebras.MetaTheory.ComplementClass
import LeanFlagAlgebras.MetaTheory.MeasureUniqueness

/-! # Root-plantability is invariant under graph complementation (paper `lem:complementation`)

This is the **capstone** (Layer 4) of `lem:complementation`.  Layers 1–3 build, from
`MetaTheory/FlagComplement.lean`, `MetaTheory/ComplementHom.lean` and
`MetaTheory/ComplementClass.lean`:

* the complementation functor on flags and the density invariances `flagDensity₁_compl`,
  `downwardNormalizingFactor_compl`, `unlabel_compl`;
* the *complement homomorphism* `complHom : PositiveHom σ → PositiveHom σᶜ` and the
  homeomorphism `complHomeo : PositiveHomSpace σ ≃ₜ PositiveHomSpace σᶜ`;
* the transfer of the constrained quotient space, `complHomeo_image_Qσ`.

Here we close the loop at the **measure-theoretic** level.  Writing `complBase φ₀` for the
empty-type complement of a base homomorphism, the heart of the file is the pushforward identity

> `Measure.map complHomeo ℙ[φ₀] = ℙ[complBase φ₀]`  (`complHomeo_map_eq`),

proved through `measure_eq_of_integral_flag_eq`: both sides integrate every flag `f` to the same
value, which (by linearity, reducing to a single basis vector) is the random-extension expectation
`(φ₀ ⟦f⟧₀) / (φ₀ ⟦1⟧₀)` recomputed in the complement world.  The numerator and denominator agree
because complementing every graph in sight is a density-preserving bijection
(`numerator_downward_eq`, `complBase_one_downward`).

Pushing this through supports and closures yields `complHomeo_image_Sσ` — `complHomeo` carries the
root-planting set of a hereditary class onto that of its complement — and, together with
`complHomeo_image_Qσ`, the capstone

> `RootPlantable (hc.constraintOf σ) ↔ RootPlantable ((hc.compl).constraintOf σᶜ)`

(`complementation_invariance`), specialised at the one-vertex type to
`complementation_invariance_oneVertex`, matching the paper's final sentence.
-/

open MeasureTheory

namespace FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## A. Generic transport helpers across the type-index equality

Complementation changes the type index `σ ↦ σᶜ`, and at the empty type the propositional
`(∅ₜ)ᶜ = ∅ₜ` (`emptyType_compl`) is *not* definitional.  These small `Eq.rec`/`HEq` helpers carry
flags, flag-algebra basis vectors and positive homomorphisms across such a type equality. -/

/-- Transporting a value across a type-index equality is heterogeneously equal to it. -/
theorem eqRec_heq_self {α : Sort _} {a b : α} (h : a = b) {motive : α → Sort _} (x : motive a) :
    HEq (h ▸ x) x := by subst h; rfl

/-- Transporting a positive homomorphism along `h : τ = τ'` and applying it to `f` equals applying
the original homomorphism to the back-transported `f`. -/
theorem posHom_eqRec_apply {τ τ' : FlagType (Fin n₀)} (h : τ = τ')
    (φ : PositiveHom τ) (f : FlagAlgebra τ') :
    (h ▸ φ : PositiveHom τ') f = φ (h ▸ f) := by subst h; rfl

/-- Transporting a basis-vector flag-algebra element along `h : τ = τ'` (in the `τ' → τ` direction)
is the basis vector of the transported flag. -/
theorem flagAlgebra_eqRec_basisVector_rev {τ τ' : FlagType (Fin n₀)} (h : τ = τ')
    (D : FinFlag τ') :
    (h ▸ (⟦basisVector D⟧ : FlagAlgebra τ') : FlagAlgebra τ) = ⟦basisVector (h ▸ D)⟧ := by
  subst h; rfl

/-- Transporting a sized flag `⟨n, F⟩` along a type-index equality keeps the size and transports the
flag. -/
theorem finFlag_eqRec_mk {τ ρ : FlagType (Fin n₀)} (h : τ = ρ) {n : ℕ} (F : Flag τ (Fin n)) :
    (h ▸ (⟨n, F⟩ : FinFlag τ) : FinFlag ρ) = ⟨n, h ▸ F⟩ := by subst h; rfl

/-- `Flag.compl` commutes with transport along a type-index equality. -/
theorem flag_compl_eqRec_comm {V : Type} {τ ρ : FlagType (Fin n₀)} (h : τ = ρ) (z : Flag τ V) :
    Flag.compl (h ▸ z : Flag ρ V) = (congrArg (·ᶜ) h) ▸ Flag.compl z := by subst h; rfl

/-- `FinFlag.compl` commutes with transport along a type-index equality. -/
theorem compl_eqRec_comm {τ ρ : FlagType (Fin n₀)} (h : τ = ρ) (z : FinFlag τ) :
    FinFlag.compl (h ▸ z : FinFlag ρ) = (congrArg (·ᶜ) h) ▸ FinFlag.compl z := by subst h; rfl

/-- `Flag.compl` is injective (it has a left inverse `Flag.uncompl`). -/
theorem flag_compl_inj {V : Type} {τ : FlagType (Fin n₀)} :
    Function.Injective (Flag.compl : Flag τ V → _) := by
  intro a b hab
  have := congrArg Flag.uncompl hab
  rwa [Flag.uncompl_compl, Flag.uncompl_compl] at this

/-- `FinFlag.compl` is injective. -/
theorem finFlag_compl_inj {τ : FlagType (Fin n₀)} :
    Function.Injective (FinFlag.compl : FinFlag τ → _) := by
  intro a b hab
  have := congrArg FinFlag.uncompl hab
  rwa [FinFlag.uncompl_compl, FinFlag.uncompl_compl] at this

/-- Heterogeneous congruence for the flag quotient across a type-index change. -/
theorem flag_mk_heq {V : Type} {σ' σ : FlagType (Fin n₀)} (hσ : σ' = σ)
    {G' : LabeledGraph σ' V} {G : LabeledGraph σ V} (hG : HEq G' G) :
    HEq (⟦G'⟧ : Flag σ' V) (⟦G⟧ : Flag σ V) := by subst hσ; rw [eq_of_heq hG]

/-- `Flag.compl` is a heterogeneous involution (modulo the propositional `σᶜᶜ = σ`). -/
theorem flag_compl_compl_heq {V : Type} {τ : FlagType (Fin n₀)} (F : Flag τ V) :
    HEq (Flag.compl (Flag.compl F)) F := by
  rcases Quotient.exists_rep F with ⟨G, rfl⟩
  rw [Flag.compl_mk, Flag.compl_mk]
  exact flag_mk_heq (_root_.compl_compl τ) (LabeledGraph.compl_compl G)

/-- Heterogeneous congruence for sized flags across a type-index change. -/
theorem finFlag_mk_heq {σ' σ : FlagType (Fin n₀)} (hσ : σ' = σ) {n : ℕ}
    {x : Flag σ' (Fin n)} {y : Flag σ (Fin n)} (hxy : HEq x y) :
    HEq (⟨n, x⟩ : FinFlag σ') (⟨n, y⟩ : FinFlag σ) := by subst hσ; rw [eq_of_heq hxy]

/-- `FinFlag.compl` is a heterogeneous involution (modulo the propositional `σᶜᶜ = σ`). -/
theorem finFlag_compl_compl_heq {τ : FlagType (Fin n₀)} (D : FinFlag τ) :
    HEq (FinFlag.compl (FinFlag.compl D)) D := by
  obtain ⟨n, F⟩ := D
  exact finFlag_mk_heq (_root_.compl_compl τ) (flag_compl_compl_heq F)

namespace MetaTheory

/-! ## B. The empty-type complement involution on flags

`D0compl` is the graph complement of an unlabelled (empty-type) sized flag; it is the empty-type
shadow of `FinFlag.compl`, with the `(∅ₜ)ᶜ = ∅ₜ` transport built in.  `numerator_unlabel_id`
records that complementing then unlabelling agrees with unlabelling the un-complement, the key
combinatorial identity behind the numerator equality. -/

/-- The graph complement of an unlabelled sized flag, landing back at the empty type via
`emptyType_compl`. -/
noncomputable def D0compl (D : FinFlag (∅ₜ : FlagType (Fin 0))) : FinFlag ∅ₜ :=
  emptyType_compl ▸ D.compl

/-- Complementing the unlabelling of a `σᶜ`-flag (and transporting back to `∅ₜ`) gives the
unlabelling of its un-complement. -/
theorem numerator_unlabel_id (G : FinFlag σᶜ) :
    (emptyType_compl ▸ (unlabel G.2).compl : Flag ∅ₜ (Fin G.1)) = unlabel G.2.uncompl := by
  apply flag_compl_inj
  rw [flag_compl_eqRec_comm emptyType_compl (unlabel G.2).compl]
  have key := unlabel_compl (σ := σ) G.2.uncompl
  rw [Flag.compl_uncompl] at key
  apply eq_of_heq
  refine HEq.trans
    (@eqRec_heq_self _ _ _ (congrArg (·ᶜ) emptyType_compl) (fun τ => Flag τ (Fin G.1))
      (unlabel G.2).compl.compl) ?_
  refine HEq.trans (flag_compl_compl_heq (unlabel G.2)) ?_
  rw [key]
  exact @eqRec_heq_self _ _ _ emptyType_compl (fun τ => Flag τ (Fin G.1)) (unlabel G.2.uncompl).compl

/-- `D0compl` of the unlabelling of a `σᶜ`-flag is the unlabelling of its un-complement. -/
theorem D0compl_unlabel (G : FinFlag σᶜ) :
    D0compl (⟨G.1, unlabel G.2⟩ : FinFlag ∅ₜ) = (⟨G.1, unlabel G.2.uncompl⟩ : FinFlag ∅ₜ) := by
  unfold D0compl
  show (emptyType_compl ▸ (⟨G.1, (unlabel G.2).compl⟩ : FinFlag (∅ₜ)ᶜ) : FinFlag ∅ₜ)
      = ⟨G.1, unlabel G.2.uncompl⟩
  rw [finFlag_eqRec_mk emptyType_compl (unlabel G.2).compl, numerator_unlabel_id]

/-- `D0compl` of the type-graph flag of `σᶜ` is the type-graph flag of `σ`. -/
theorem D0compl_emptyType :
    D0compl (⟨n₀, σᶜ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ) = (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ) := by
  have h := D0compl_unlabel (1 : FinFlag σᶜ)
  rw [flagType_asEmptyTypeFlag_eq σ, flagType_asEmptyTypeFlag_eq σᶜ]
  rw [show (⟨n₀, unlabel (emptyFlag σᶜ)⟩ : FinFlag ∅ₜ)
        = ⟨(1 : FinFlag σᶜ).1, unlabel (1 : FinFlag σᶜ).2⟩ from rfl, h]
  show (⟨n₀, unlabel ((emptyFlag σᶜ).uncompl)⟩ : FinFlag ∅ₜ) = ⟨n₀, unlabel (emptyFlag σ)⟩
  rw [emptyFlag_uncompl]

/-! ## C. The base complement homomorphism and its evaluation law -/

/-- The **base complement homomorphism**: the empty-type un-complement of `complHom φ₀`, transported
along `(∅ₜ)ᶜ = ∅ₜ`. -/
noncomputable def complBase (φ₀ : PositiveHom ∅ₜ) : PositiveHom ∅ₜ :=
  emptyType_compl ▸ complHom φ₀

/-- Transporting `FinFlag.uncompl` of a forward transport is the backward transport of the
complement. -/
theorem uncompl_eqRec_compl (D : FinFlag (∅ₜ : FlagType (Fin 0))) :
    FinFlag.uncompl (emptyType_compl.symm ▸ D) = emptyType_compl ▸ D.compl := by
  apply finFlag_compl_inj
  rw [FinFlag.compl_uncompl, compl_eqRec_comm emptyType_compl D.compl]
  apply eq_of_heq
  refine HEq.trans (eqRec_heq_self emptyType_compl.symm D) ?_
  refine HEq.symm (HEq.trans (eqRec_heq_self (congrArg (·ᶜ) emptyType_compl) D.compl.compl) ?_)
  exact finFlag_compl_compl_heq D

/-- **Evaluation law for `complBase`.**  Its value on a basis vector `D` is `φ₀` evaluated at the
graph complement `D0compl D`. -/
theorem complBase_coe (φ₀ : PositiveHom ∅ₜ) (D : FinFlag ∅ₜ) :
    (complBase φ₀) ⟦basisVector D⟧ = φ₀ ⟦basisVector (D0compl D)⟧ := by
  unfold complBase D0compl
  rw [posHom_eqRec_apply emptyType_compl (complHom φ₀) (⟦basisVector D⟧ : FlagAlgebra ∅ₜ),
    flagAlgebra_eqRec_basisVector_rev emptyType_compl D,
    ← PositiveHom.coe_flag, complHom_coe, PositiveHom.coe_flag, ← uncompl_eqRec_compl D]

/-- `D0compl` is an involution: complementing the underlying graph twice is the identity. -/
theorem D0compl_involutive (D : FinFlag (∅ₜ : FlagType (Fin 0))) :
    D0compl (D0compl D) = D := by
  unfold D0compl
  rw [compl_eqRec_comm emptyType_compl D.compl]
  apply eq_of_heq
  refine HEq.trans (eqRec_heq_self emptyType_compl _) ?_
  refine HEq.trans (eqRec_heq_self (congrArg (·ᶜ) emptyType_compl) D.compl.compl) ?_
  exact finFlag_compl_compl_heq D

/-- `complBase` is an involution: `complBase (complBase φ₀) = φ₀`.  (At the empty type the base
complement is its own inverse, modulo `emptyType_compl`.) -/
theorem complBase_involutive (φ₀ : PositiveHom ∅ₜ) : complBase (complBase φ₀) = φ₀ := by
  apply PositiveHom.coe_injective
  apply (DFunLike.coe_injective (F := FlagDensitySpace ∅ₜ))
  funext D
  show (complBase (complBase φ₀)).coe D = φ₀.coe D
  rw [PositiveHom.coe_flag, PositiveHom.coe_flag, complBase_coe, complBase_coe, D0compl_involutive]

/-! ## D. The numerator, denominator and type-density equalities

These say the random-extension expectation `(φ₀ ⟦f⟧₀)/(φ₀ ⟦1⟧₀)` is computed identically in the
complement world: complementing every graph in the `downward` (unlabelling) operator is a
density-preserving bijection. -/

/-- The unlabelling weight is unchanged under un-complementation. -/
theorem dnf_uncompl (G : FinFlag σᶜ) :
    downwardNormalizingFactor G.2.uncompl = downwardNormalizingFactor G.2 := by
  conv_rhs => rw [← Flag.compl_uncompl G.2]
  rw [downwardNormalizingFactor_compl]

/-- **The numerator equality.**  Down-averaging the un-complement `G.uncompl` of a `σᶜ`-flag under
`φ₀` equals down-averaging `G` under `complBase φ₀`. -/
theorem numerator_downward_eq (φ₀ : PositiveHom ∅ₜ) (G : FinFlag σᶜ) :
    φ₀ ⟦(⟦basisVector G.uncompl⟧ : FlagAlgebra σ)⟧₀
      = (complBase φ₀) ⟦(⟦basisVector G⟧ : FlagAlgebra σᶜ)⟧₀ := by
  rw [downward_basisVector G.uncompl, downward_basisVector G,
    PositiveHom.map_smul, PositiveHom.map_smul]
  show (downwardNormalizingFactor G.2.uncompl : ℝ) * φ₀ ⟦basisVector ⟨G.1, unlabel G.2.uncompl⟩⟧
     = (downwardNormalizingFactor G.2 : ℝ) * (complBase φ₀) ⟦basisVector ⟨G.1, unlabel G.2⟩⟧
  rw [dnf_uncompl, complBase_coe φ₀ ⟨G.1, unlabel G.2⟩, D0compl_unlabel G]

/-- **The denominator equality.**  Down-averaging `1` under `φ₀` (in the `σ`-algebra) equals
down-averaging `1` under `complBase φ₀` (in the `σᶜ`-algebra). -/
theorem complBase_one_downward (φ₀ : PositiveHom ∅ₜ) :
    φ₀ ⟦(1 : FlagAlgebra σ)⟧₀ = (complBase φ₀) ⟦(1 : FlagAlgebra σᶜ)⟧₀ := by
  have h := numerator_downward_eq φ₀ (1 : FinFlag σᶜ)
  rw [finFlag_one_uncompl] at h
  -- `(1 : FlagAlgebra σ) = ⟦basisVector (1 : FinFlag σ)⟧`, ditto for `σᶜ`, both definitionally.
  exact h

/-- **The type-density equality.**  `complBase φ₀` assigns the type graph `σᶜ` the same density
that `φ₀` assigns the type graph `σ`. -/
theorem complBase_type_eq (φ₀ : PositiveHom ∅ₜ) :
    (complBase φ₀) ⟨σᶜ⟩₀ = φ₀ ⟨σ⟩₀ := by
  show (complBase φ₀) ⟦basisVector (⟨n₀, σᶜ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ)⟧
     = φ₀ ⟦basisVector (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ)⟧
  rw [complBase_coe, D0compl_emptyType]

/-- Admissibility transfers: if `φ₀ ⟨σ⟩₀ > 0` then `complBase φ₀ ⟨σᶜ⟩₀ > 0`, so the random extension
`ℙ[complBase φ₀]` is well-defined. -/
theorem complBase_type_pos (φ₀ : PositiveHom ∅ₜ) (hσ : φ₀ ⟨σ⟩₀ > 0) :
    (complBase φ₀) ⟨σᶜ⟩₀ > 0 := by
  rw [complBase_type_eq]; exact hσ

/-! ## E. The measure pushforward (the crux, paper §5/Step 1)

`complHomeo` carries the random extension `ℙ[φ₀]` exactly onto `ℙ[complBase φ₀]`.  By
`measure_eq_of_integral_flag_eq` it suffices to match flag integrals; by linearity this reduces to a
single basis vector, where `numerator_downward_eq` and `complBase_one_downward` close it. -/

/-- Every flag evaluation is integrable against a probability measure on the (compact) homomorphism
space. -/
theorem evalIntegrable (μ : Measure (PositiveHomSpace σ)) [IsProbabilityMeasure μ]
    (f : FlagAlgebra σ) :
    Integrable (fun χ : PositiveHomSpace σ => (PositiveHomSpace.toPosHom χ) f) μ :=
  BoundedContinuousFunction.integrable _
    (BoundedContinuousFunction.mkOfCompact (evalContinuousMap f))

/-- **Per-basis-vector expectation identity.**  The complement-world expectation of `⟦basisVector G⟧`
under `complBase φ₀` equals the expectation of its un-complement under `φ₀`. -/
theorem expectation_basisVector_eq (φ₀ : PositiveHom ∅ₜ) (hσ : φ₀ ⟨σ⟩₀ > 0)
    (hσ' : (complBase φ₀) ⟨σᶜ⟩₀ > 0) (G : FinFlag σᶜ) :
    ∫ χ, (complHom (PositiveHomSpace.toPosHom χ)) ⟦basisVector G⟧
        ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ))
      = ∫ η, (PositiveHomSpace.toPosHom η) ⟦basisVector G⟧
          ∂(ℙ[complBase φ₀] : Measure (PositiveHomSpace σᶜ)) := by
  have hL :
      (fun χ : PositiveHomSpace σ => (complHom (PositiveHomSpace.toPosHom χ)) ⟦basisVector G⟧)
        = (fun χ : PositiveHomSpace σ => (PositiveHomSpace.toPosHom χ) ⟦basisVector G.uncompl⟧) := by
    funext χ
    rw [← PositiveHom.coe_flag, complHom_coe, PositiveHom.coe_flag]
  rw [hL, probMeasure_extend_emptyType_positiveHom_spec hσ ⟦basisVector G.uncompl⟧,
    probMeasure_extend_emptyType_positiveHom_spec hσ' ⟦basisVector G⟧,
    numerator_downward_eq φ₀ G, complBase_one_downward (σ := σ) φ₀]

/-- **Per-flag expectation identity.**  Extends `expectation_basisVector_eq` to all `f` by
linearity (the integral and `complHom`/`toPosHom` are all ℝ-linear in `f`). -/
theorem expectation_flag_eq (φ₀ : PositiveHom ∅ₜ) (hσ : φ₀ ⟨σ⟩₀ > 0)
    (hσ' : (complBase φ₀) ⟨σᶜ⟩₀ > 0) (f : FlagAlgebra σᶜ) :
    ∫ χ, (complHom (PositiveHomSpace.toPosHom χ)) f ∂(ℙ[φ₀] : Measure (PositiveHomSpace σ))
      = ∫ η, (PositiveHomSpace.toPosHom η) f ∂(ℙ[complBase φ₀] : Measure (PositiveHomSpace σᶜ)) := by
  rcases Quotient.exists_rep f with ⟨frep, rfl⟩
  -- Rewrite each integrand as a finite sum of scalar multiples of basis-vector evaluations.
  have hLHS : (fun χ : PositiveHomSpace σ => (complHom (PositiveHomSpace.toPosHom χ)) ⟦frep⟧)
      = (fun χ => ∑ F ∈ frep.support,
          frep F • (complHom (PositiveHomSpace.toPosHom χ)) ⟦basisVector F⟧) := by
    funext χ
    conv_lhs => rw [flagVector_eq_sum_basisVector frep]
    rw [sum_quot, PositiveHom.map_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [smul_quot, PositiveHom.map_smul, smul_eq_mul]
  have hRHS : (fun η : PositiveHomSpace σᶜ => (PositiveHomSpace.toPosHom η) ⟦frep⟧)
      = (fun η => ∑ F ∈ frep.support,
          frep F • (PositiveHomSpace.toPosHom η) ⟦basisVector F⟧) := by
    funext η
    conv_lhs => rw [flagVector_eq_sum_basisVector frep]
    rw [sum_quot, PositiveHom.map_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [smul_quot, PositiveHom.map_smul, smul_eq_mul]
  rw [hLHS, hRHS,
    integral_finset_sum frep.support, integral_finset_sum frep.support]
  · refine Finset.sum_congr rfl fun F _ => ?_
    rw [integral_smul, integral_smul]
    congr 1
    exact expectation_basisVector_eq φ₀ hσ hσ' F
  · intro F _
    have : (fun η : PositiveHomSpace σᶜ => frep F • (PositiveHomSpace.toPosHom η) ⟦basisVector F⟧)
        = (fun η => (PositiveHomSpace.toPosHom η) ⟦frep F • basisVector F⟧) := by
      funext η; rw [smul_quot, PositiveHom.map_smul, smul_eq_mul]
    rw [this]
    exact evalIntegrable _ _
  · intro F _
    have : (fun χ : PositiveHomSpace σ =>
          frep F • (complHom (PositiveHomSpace.toPosHom χ)) ⟦basisVector F⟧)
        = (fun χ => (PositiveHomSpace.toPosHom χ) ⟦frep F • basisVector F.uncompl⟧) := by
      funext χ
      rw [smul_quot, PositiveHom.map_smul, smul_eq_mul, ← PositiveHom.coe_flag, complHom_coe,
        PositiveHom.coe_flag]
    rw [this]
    exact evalIntegrable _ _

/-- **The measure pushforward (the crux).**  Pushing the random extension `ℙ[φ₀]` forward along the
complement homeomorphism yields exactly the random extension of `complBase φ₀`. -/
theorem complHomeo_map_eq (φ₀ : PositiveHom ∅ₜ) (hσ : φ₀ ⟨σ⟩₀ > 0)
    (hσ' : (complBase φ₀) ⟨σᶜ⟩₀ > 0) :
    (ℙ[φ₀] : ProbabilityMeasure (PositiveHomSpace σ)).map
        (complHomeo (σ := σ)).continuous.measurable.aemeasurable
      = ℙ[complBase φ₀] := by
  apply measure_eq_of_integral_flag_eq
  intro f
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (complHomeo (σ := σ)).continuous.measurable.aemeasurable
      (continuous_eval f).aestronglyMeasurable]
  -- the pushforward integrand `(toPosHom (complHomeo χ)) f = (complHom (toPosHom χ)) f`
  have hcompl : (fun χ : PositiveHomSpace σ =>
        (PositiveHomSpace.toPosHom (complHomeo χ)) f)
      = (fun χ => (complHom (PositiveHomSpace.toPosHom χ)) f) := by
    funext χ
    rw [show PositiveHomSpace.toPosHom (complHomeo χ) = complHom (PositiveHomSpace.toPosHom χ)
        from toPosHom_posHomPoint _]
  rw [hcompl]
  exact expectation_flag_eq φ₀ hσ hσ' f

/-! ## F. Support, admissibility and the index bijection (paper §5/Steps 2–3) -/

/-- A homeomorphism maps the support of a measure onto the support of the pushforward measure. -/
theorem homeo_image_support {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (e : X ≃ₜ Y) (μ : Measure X) :
    e '' μ.support = (μ.map e).support := by
  ext y
  rw [Measure.support_eq_forall_isOpen, Measure.support_eq_forall_isOpen]
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩ U hU hUopen
    rw [Measure.map_apply e.continuous.measurable hUopen.measurableSet]
    exact hx _ hU (hUopen.preimage e.continuous)
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    intro U hU hUopen
    have hopen : IsOpen (e '' U) := e.isOpenMap _ hUopen
    have hymem : y ∈ e '' U := ⟨e.symm y, hU, by simp⟩
    have := hy _ hymem hopen
    rwa [Measure.map_apply e.continuous.measurable hopen.measurableSet, e.preimage_image] at this

/-- The underlying-graph membership of the complement class on `D` matches that of the original
class on `D0compl D` (the graph complement). -/
theorem underlyingMem_compl_iff (hc : HeredClass) (D : FinFlag (∅ₜ : FlagType (Fin 0))) :
    (hc.compl).underlyingMem D.2 ↔ hc.underlyingMem (D0compl D).2 := by
  obtain ⟨n, Dq⟩ := D
  rcases Quotient.exists_rep Dq with ⟨Drep, rfl⟩
  rw [hc.compl.underlyingMem_mk Drep, hc.compl_Mem]
  show hc.Mem (Drep.graphᶜ) ↔ hc.underlyingMem (D0compl ⟨n, ⟦Drep⟧⟩).2
  have hD0 : D0compl (⟨n, (⟦Drep⟧ : Flag ∅ₜ (Fin n))⟩ : FinFlag ∅ₜ)
      = ⟨n, (⟦emptyType_compl ▸ Drep.compl⟧ : Flag ∅ₜ (Fin n))⟩ := by
    unfold D0compl
    rw [show (FinFlag.compl (⟨n, (⟦Drep⟧ : Flag ∅ₜ (Fin n))⟩ : FinFlag ∅ₜ))
          = ⟨n, (⟦Drep.compl⟧ : Flag (∅ₜ)ᶜ (Fin n))⟩ from by
            simp only [FinFlag.compl, Flag.compl_mk]]
    rw [finFlag_eqRec_mk emptyType_compl (⟦Drep.compl⟧ : Flag (∅ₜ)ᶜ (Fin n)),
      flag_eqRec_mk emptyType_compl Drep.compl]
  rw [hD0]
  show hc.Mem (Drep.graphᶜ) ↔ hc.underlyingMem (⟦emptyType_compl ▸ Drep.compl⟧ : Flag ∅ₜ (Fin n))
  rw [hc.underlyingMem_mk, labeledGraph_eqRec_graph emptyType_compl Drep.compl,
    LabeledGraph.compl_graph]

/-- **Admissibility (`Q₀`) transfer.**  `φ₀` is a constrained unlabelled limit for `hc` iff
`complBase φ₀` is one for `hc.compl`.  This is the `D0compl`-reindexing of the empty-type
forbidden-graph condition. -/
theorem complBase_mem_Q0 (hc : HeredClass) (φ₀ : PositiveHom ∅ₜ) :
    posHomPoint φ₀ ∈ Qσ (hc.constraintOf σ).forb0
      ↔ posHomPoint (complBase φ₀) ∈ Qσ ((hc.compl).constraintOf σᶜ).forb0 := by
  rw [mem_Qσ_iff, mem_Qσ_iff]
  constructor
  · intro hL D hD
    rw [posHomPoint_val_apply, complBase_coe, ← posHomPoint_val_apply]
    apply hL
    show ¬ hc.underlyingMem (D0compl D).2
    have hD' : ¬ (hc.compl).underlyingMem D.2 := hD
    rwa [underlyingMem_compl_iff] at hD'
  · intro hR D hD
    have hRD := hR (D0compl D)
    rw [posHomPoint_val_apply, complBase_coe, D0compl_involutive, ← posHomPoint_val_apply] at hRD
    apply hRD
    show ¬ (hc.compl).underlyingMem (D0compl D).2
    rw [underlyingMem_compl_iff, D0compl_involutive]
    exact hD

/-- The random extension measure depends only on the base homomorphism, not on the chosen
positivity proof (proof irrelevance through `Classical.choose`). -/
theorem probMeasure_congr {φ φ' : PositiveHom ∅ₜ} (h : φ = φ')
    (hσ : φ ⟨σ⟩₀ > 0) (hσ' : φ' ⟨σ⟩₀ > 0) :
    probMeasure_extend_emptyType_positiveHom φ hσ (σ := σ)
      = probMeasure_extend_emptyType_positiveHom φ' hσ' := by subst h; rfl

/-- The reverse type-density equality: `complBase` carries the density of `σᶜ` back to that of `σ`. -/
theorem complBase_type_eq' (φ₀ : PositiveHom ∅ₜ) :
    (complBase φ₀) ⟨σ⟩₀ = φ₀ ⟨σᶜ⟩₀ := by
  have hh := congrArg D0compl (D0compl_emptyType (σ := σ))
  rw [D0compl_involutive] at hh
  show (complBase φ₀) ⟦basisVector (⟨n₀, σ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ)⟧
     = φ₀ ⟦basisVector (⟨n₀, σᶜ.toEmptyTypeFlag⟩ : FinFlag ∅ₜ)⟧
  rw [complBase_coe, hh.symm]

/-- Reverse admissibility for the type density: if `φ₀ ⟨σᶜ⟩₀ > 0` then `complBase φ₀ ⟨σ⟩₀ > 0`. -/
theorem complBase_type_pos' (φ₀ : PositiveHom ∅ₜ) (hσ : φ₀ ⟨σᶜ⟩₀ > 0) :
    (complBase φ₀) ⟨σ⟩₀ > 0 := by rw [complBase_type_eq']; exact hσ

/-- **Support transfer.**  `complHomeo` carries the support of `ℙ[φ₀]` onto the support of
`ℙ[complBase φ₀]` — the support-level shadow of `complHomeo_map_eq`. -/
theorem complHomeo_image_support (φ₀ : PositiveHom ∅ₜ) (hσ : φ₀ ⟨σ⟩₀ > 0)
    (hσ' : (complBase φ₀) ⟨σᶜ⟩₀ > 0) :
    complHomeo ''
        (probMeasure_extend_emptyType_positiveHom φ₀ hσ : Measure (PositiveHomSpace σ)).support
      = (probMeasure_extend_emptyType_positiveHom (complBase φ₀) hσ'
          : Measure (PositiveHomSpace σᶜ)).support := by
  rw [homeo_image_support complHomeo
    (probMeasure_extend_emptyType_positiveHom φ₀ hσ : Measure (PositiveHomSpace σ))]
  have hmeas : (probMeasure_extend_emptyType_positiveHom φ₀ hσ
        : Measure (PositiveHomSpace σ)).map complHomeo
      = (probMeasure_extend_emptyType_positiveHom (complBase φ₀) hσ'
          : Measure (PositiveHomSpace σᶜ)) := by
    rw [← ProbabilityMeasure.toMeasure_map
      (probMeasure_extend_emptyType_positiveHom φ₀ hσ)
      complHomeo.continuous.measurable.aemeasurable, complHomeo_map_eq φ₀ hσ hσ']
  rw [hmeas]

/-- **The root-planting set transfers (paper §5/Step 3).**  `complHomeo` carries the root-planting
set of `hc` onto that of its complement.  The closure passes through the homeomorphism, the supports
transfer term-by-term (`complHomeo_image_support`), and the union is reindexed by the involution
`complBase` together with the admissibility transfer `complBase_mem_Q0`. -/
theorem complHomeo_image_Sσ (hc : HeredClass) (σ : FlagType (Fin n₀)) :
    complHomeo '' (Sσ (hc.constraintOf σ)) = Sσ ((hc.compl).constraintOf σᶜ) := by
  unfold Sσ
  rw [Homeomorph.image_closure]
  congr 1
  apply Set.Subset.antisymm
  · -- forward: every admissible `φ₀` for `hc` yields `complBase φ₀`, admissible for `hc.compl`
    rw [Set.image_iUnion]
    apply Set.iUnion_subset; intro φ₀
    rw [Set.image_iUnion]; apply Set.iUnion_subset; intro hφ₀
    rw [Set.image_iUnion]; apply Set.iUnion_subset; intro hσpos
    rw [complHomeo_image_support φ₀ hσpos (complBase_type_pos φ₀ hσpos)]
    refine Set.subset_iUnion_of_subset (complBase φ₀) ?_
    refine Set.subset_iUnion_of_subset ((complBase_mem_Q0 hc φ₀).mp hφ₀) ?_
    exact Set.subset_iUnion (fun (h : (complBase φ₀) ⟨σᶜ⟩₀ > 0) =>
      (probMeasure_extend_emptyType_positiveHom (complBase φ₀) h
        : Measure (PositiveHomSpace σᶜ)).support) (complBase_type_pos φ₀ hσpos)
  · -- backward: every admissible `ψ₀` for `hc.compl` arises as `complBase (complBase ψ₀)`
    apply Set.iUnion_subset; intro ψ₀
    apply Set.iUnion_subset; intro hψ₀
    apply Set.iUnion_subset; intro hσpos'
    have hφadm : posHomPoint (complBase ψ₀) ∈ Qσ (hc.constraintOf σ).forb0 := by
      rw [complBase_mem_Q0 hc (complBase ψ₀), complBase_involutive]; exact hψ₀
    have hφtype : (complBase ψ₀) ⟨σ⟩₀ > 0 := complBase_type_pos' ψ₀ hσpos'
    have hinv : (probMeasure_extend_emptyType_positiveHom (complBase (complBase ψ₀))
            ((complBase_involutive ψ₀).symm ▸ hσpos') : Measure (PositiveHomSpace σᶜ))
        = (probMeasure_extend_emptyType_positiveHom ψ₀ hσpos'
            : Measure (PositiveHomSpace σᶜ)) :=
      congrArg _ (probMeasure_congr (complBase_involutive ψ₀) _ hσpos')
    have hsupp : (probMeasure_extend_emptyType_positiveHom ψ₀ hσpos'
            : Measure (PositiveHomSpace σᶜ)).support
        = complHomeo '' (probMeasure_extend_emptyType_positiveHom (complBase ψ₀) hφtype
            : Measure (PositiveHomSpace σ)).support := by
      rw [complHomeo_image_support (complBase ψ₀) hφtype
        ((complBase_involutive ψ₀).symm ▸ hσpos'), hinv]
    rw [hsupp]
    apply Set.image_mono
    refine Set.subset_iUnion_of_subset (complBase ψ₀) ?_
    refine Set.subset_iUnion_of_subset hφadm ?_
    exact Set.subset_iUnion (fun (h : (complBase ψ₀) ⟨σ⟩₀ > 0) =>
      (probMeasure_extend_emptyType_positiveHom (complBase ψ₀) h
        : Measure (PositiveHomSpace σ)).support) hφtype

/-! ## G. The capstone and its one-vertex corollary (paper §5/Steps 4–5) -/

/-- **Root-plantability is invariant under complementation** (paper `lem:complementation`).  Applying
the bijection `complHomeo` to both sides of `S_σ = Q_σ` and rewriting the two images by
`complHomeo_image_Sσ` (Step 3) and `complHomeo_image_Qσ` (Layer 3) trades the root-plantability of
`hc` at `σ` for that of `hc.compl` at `σᶜ`. -/
theorem complementation_invariance (hc : HeredClass) (σ : FlagType (Fin n₀)) :
    RootPlantable (hc.constraintOf σ) ↔ RootPlantable ((hc.compl).constraintOf σᶜ) := by
  unfold RootPlantable
  rw [← complHomeo_image_Sσ hc σ, ← complHomeo_image_Qσ hc σ]
  exact (Set.image_eq_image complHomeo.injective).symm

/-- The one-vertex (edgeless) type is its own complement: on `Fin 1` there are no distinct pairs. -/
theorem botFlagType_one_compl : (⊥ : FlagType (Fin 1))ᶜ = ⊥ := by
  ext u v
  rw [SimpleGraph.compl_adj, SimpleGraph.bot_adj]
  constructor
  · rintro ⟨hne, _⟩
    exact absurd (Subsingleton.elim u v) hne
  · exact False.elim

/-- **The one-vertex corollary** (the paper's final sentence): root-plantability of a hereditary
class at the single-vertex type holds iff it holds for the complement class, since the one-vertex
type is self-complementary. -/
theorem complementation_invariance_oneVertex (hc : HeredClass) :
    RootPlantable (hc.constraintOf (⊥ : FlagType (Fin 1)))
      ↔ RootPlantable ((hc.compl).constraintOf (⊥ : FlagType (Fin 1))) := by
  have h := complementation_invariance hc (⊥ : FlagType (Fin 1))
  rw [botFlagType_one_compl] at h
  exact h

end MetaTheory

end FlagAlgebras
