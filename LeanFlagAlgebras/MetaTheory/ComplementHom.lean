import LeanFlagAlgebras.MetaTheory.FlagComplement
import LeanFlagAlgebras.MetaTheory.SupportClosure

/-! # Complementation is a homeomorphism of positive-homomorphism spaces

Layer 2 of the formalisation of `lem:complementation` (*root-plantability is complementation
invariant*).  Building on `MetaTheory/FlagComplement.lean` (which proves that labelled flag
densities are unchanged by complementing every graph in sight and the type `σ` by `σᶜ`), this file
shows:

* **The complement of a positive homomorphism is a positive homomorphism.**  Given `φ : PositiveHom σ`
  its *complement profile* `G ↦ φ.coe G.uncompl` (a density profile on `σᶜ`-flags) again satisfies
  the chain rule / normalisation / multiplicativity (`zeroSpaceProp`/`oneProp`/`mulProp`), so it
  packages into `complHom φ : PositiveHom σᶜ`.  The density-invariance facts `flagDensity₁_compl` /
  `flagDensity₂_compl` are exactly what is needed to reindex the defining sums.
* **Symmetric inverse.**  `uncomplHom η : PositiveHom σ` runs the same construction with the roles
  of `compl`/`uncompl` swapped, and `complHom`/`uncomplHom` are mutually inverse
  (`uncomplHom_complHom`, `complHom_uncomplHom`) — cleanly, with no `σᶜᶜ` transport, thanks to the
  honest `Flag.uncompl_compl`/`Flag.compl_uncompl` laws.
* **The homeomorphism.**  Reflecting these maps onto the (compact metric) homomorphism spaces gives
  `complHomeo : PositiveHomSpace σ ≃ₜ PositiveHomSpace σᶜ`, acting by `(complHomeo χ).val G =
  χ.val G.uncompl`.  Continuity in both directions is coordinatewise: each coordinate of the image is
  a single coordinate of the source.

The pivotal API is `complHom`/`uncomplHom` (the algebraic layer) and `complHomeo`/`complHomeo_val`
(the topological layer), which downstream files use to transport root-plantability across
complementation.
-/

open Classical

namespace FlagAlgebras

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## A. Lifting `uncompl` to flags and the reindexing bijection -/

/-- Complementation in the reverse direction respects labelled-graph isomorphism: an iso of
`σᶜ`-labelled graphs un-complements to an iso of `σ`-labelled graphs.  Obtained from
`nonempty_flagEqv_compl_iff` together with the honest `compl_uncompl` law. -/
theorem flagEqv_uncompl {V : Type} {G G' : LabeledGraph σᶜ V} (h : G ∼f G') :
    G.uncompl ∼f G'.uncompl := by
  apply (nonempty_flagEqv_compl_iff G.uncompl G'.uncompl).mpr
  rw [LabeledGraph.compl_uncompl, LabeledGraph.compl_uncompl]
  exact h

/-- The complement of a flag, in the reverse direction: lift `LabeledGraph.uncompl` through the
flag quotient. -/
noncomputable def Flag.uncompl {V : Type} : Flag σᶜ V → Flag σ V :=
  Quotient.lift (fun G : LabeledGraph σᶜ V => (⟦G.uncompl⟧ : Flag σ V))
    fun _ _ h => Quotient.sound (flagEqv_uncompl h)

@[simp]
theorem Flag.uncompl_mk {V : Type} (G : LabeledGraph σᶜ V) :
    Flag.uncompl (⟦G⟧ : Flag σᶜ V) = (⟦G.uncompl⟧ : Flag σ V) := rfl

/-- `compl` then `uncompl` is the identity on `Flag σ V`. -/
theorem Flag.uncompl_compl {V : Type} (F : Flag σ V) : F.compl.uncompl = F := by
  rcases Quotient.exists_rep F with ⟨G, rfl⟩
  rw [Flag.compl_mk, Flag.uncompl_mk, LabeledGraph.uncompl_compl]

/-- `uncompl` then `compl` is the identity on `Flag σᶜ V`. -/
theorem Flag.compl_uncompl {V : Type} (F : Flag σᶜ V) : F.uncompl.compl = F := by
  rcases Quotient.exists_rep F with ⟨G, rfl⟩
  rw [Flag.uncompl_mk, Flag.compl_mk, LabeledGraph.compl_uncompl]

/-- The un-complement of a sized flag, as a sized flag of the original type. -/
noncomputable def FinFlag.uncompl (G : FinFlag σᶜ) : FinFlag σ := ⟨G.1, G.2.uncompl⟩

@[simp]
theorem FinFlag.uncompl_compl (F : FinFlag σ) : F.compl.uncompl = F := by
  obtain ⟨n, F⟩ := F
  simp only [FinFlag.compl, FinFlag.uncompl, Flag.uncompl_compl]

@[simp]
theorem FinFlag.compl_uncompl (G : FinFlag σᶜ) : G.uncompl.compl = G := by
  obtain ⟨n, G⟩ := G
  simp only [FinFlag.uncompl, FinFlag.compl, Flag.compl_uncompl]

/-- `Flag.compl`/`Flag.uncompl` as a size-preserving bijection of sized flags. -/
noncomputable def Flag.complEquiv {ℓ : ℕ} : FlagWithSize σ ℓ ≃ FlagWithSize σᶜ ℓ where
  toFun := Flag.compl
  invFun := Flag.uncompl
  left_inv F := Flag.uncompl_compl F
  right_inv F := Flag.compl_uncompl F

@[simp]
theorem Flag.complEquiv_apply {ℓ : ℕ} (F : FlagWithSize σ ℓ) :
    (Flag.complEquiv F : FlagWithSize σᶜ ℓ) = F.compl := rfl

/-- Reindexing a sum over `σᶜ`-flags of size `ℓ` as a sum over `σ`-flags of size `ℓ`, by
complementing each summand. -/
theorem sum_flagWithSize_compl {ℓ : ℕ} (f : FlagWithSize σᶜ ℓ → ℝ) :
    ∑ G : FlagWithSize σᶜ ℓ, f G = ∑ G : FlagWithSize σ ℓ, f G.compl :=
  (Equiv.sum_comp (Flag.complEquiv (σ := σ) (ℓ := ℓ)) f).symm

namespace MetaTheory

/-! ## Genuine homomorphisms satisfy the structural profile properties

These extract `zeroSpaceProp`/`oneProp`/`mulProp` for the profile `φ.coe` of a *genuine* positive
homomorphism.  They mirror the forward direction of `positiveHomSpace_eq`. -/

theorem positiveHom_zeroSpaceProp (φ : PositiveHom σ) : zeroSpaceProp φ.coe := by
  intro F ℓ hℓ
  simp only [PositiveHom.coe_flag]
  rw [basisVector_quot_eq_sum F ℓ hℓ]
  simp_rw [PositiveHom.map_sum, PositiveHom.map_smul]

theorem positiveHom_oneProp (φ : PositiveHom σ) : oneProp φ.coe := by
  simp only [oneProp, PositiveHom.coe_flag]
  exact PositiveHom.map_one φ

theorem positiveHom_mulProp (φ : PositiveHom σ) : mulProp φ.coe := by
  intro F₁ F₂
  simp only [PositiveHom.coe_flag]
  rw [← PositiveHom.map_mul φ, ← mul_quot, flagVector_mul_eq_nested_sum]
  simp only [basisVector_support, Finset.sum_singleton, basisVector_apply_self, mul_one, one_smul]
  dsimp only [flagMul, flagMulWithSize, rat_smul_eq_real_smul]
  simp_rw [sum_quot, smul_quot, PositiveHom.map_sum, PositiveHom.map_smul]

/-! ## B. The complemented profile and its three structural properties -/

variable {σ : FlagType (Fin n₀)}

/-- The complement density profile of `φ` packaged in `FlagDensitySpace σᶜ`: each `σᶜ`-flag `G`
is sent to `φ.coe G.uncompl ∈ [0,1]`. -/
noncomputable def complementCoe (φ : PositiveHom σ) : FlagDensitySpace σᶜ :=
  { val := fun G => φ.coe G.uncompl
    property := by
      simp only [FlagDensitySpace, Set.pi_univ_Icc, Set.mem_Icc]
      exact ⟨fun G => (flagDensitySpace_mem_Icc_zero_one φ.coe G.uncompl).1,
             fun G => (flagDensitySpace_mem_Icc_zero_one φ.coe G.uncompl).2⟩ }

@[simp]
theorem complementCoe_apply (φ : PositiveHom σ) (G : FinFlag σᶜ) :
    (complementCoe φ) G = φ.coe G.uncompl := rfl

/-- The empty `σᶜ`-flag un-complements to the empty `σ`-flag. -/
theorem emptyFlag_uncompl : Flag.uncompl (emptyFlag σᶜ) = emptyFlag σ := by
  have hcompl : Flag.compl (emptyFlag σ) = emptyFlag σᶜ := by
    show Flag.compl (⟦emptyLabeledGraph σ⟧ : Flag σ (Fin n₀)) = ⟦emptyLabeledGraph σᶜ⟧
    rw [Flag.compl_mk]
    apply Quotient.sound
    refine ⟨{ graph_iso := ?_, type_preserve := ?_ }⟩
    · show (emptyLabeledGraph σ).compl.graph ≃g (emptyLabeledGraph σᶜ).graph
      exact SimpleGraph.Iso.refl
    · funext t; rfl
  rw [← hcompl, Flag.uncompl_compl]

/-- The unit `σᶜ`-flag un-complements to the unit `σ`-flag. -/
theorem finFlag_one_uncompl : (1 : FinFlag σᶜ).uncompl = (1 : FinFlag σ) := by
  apply Sigma.ext
  · rfl
  · rw [heq_eq_eq]
    show Flag.uncompl (1 : FinFlag σᶜ).2 = (1 : FinFlag σ).2
    rw [finFlag_one_snd, finFlag_one_snd, emptyFlag_uncompl]

theorem complementProfile_oneProp (φ : PositiveHom σ) : oneProp (complementCoe φ) := by
  show (complementCoe φ) (1 : FinFlag σᶜ) = 1
  rw [complementCoe_apply, finFlag_one_uncompl]
  exact positiveHom_oneProp φ

/-- A single-flag density of `σᶜ`-flags reindexed through `compl`/`uncompl`: complementing a
`σ`-flag and comparing against `F` (with `F.2.uncompl` complemented back) recovers a `σ`-density. -/
theorem flagDensity₁_uncompl_compl {ℓ : ℕ} (F : FinFlag σᶜ) (G' : FlagWithSize σ ℓ) :
    flagDensity₁ F.2 G'.compl = flagDensity₁ F.2.uncompl G' := by
  conv_lhs => rw [← Flag.compl_uncompl F.2]
  rw [flagDensity₁_compl]

theorem complementProfile_zeroSpaceProp (φ : PositiveHom σ) : zeroSpaceProp (complementCoe φ) := by
  intro F ℓ hℓ
  rw [complementCoe_apply]
  -- reindex the RHS sum over `σᶜ`-flags by complementing `σ`-flags
  rw [sum_flagWithSize_compl
      (fun G => flagDensity₁ F.2 G * (complementCoe φ) ⟨ℓ, G⟩)]
  have hsum : (∑ G' : FlagWithSize σ ℓ,
        flagDensity₁ F.2 G'.compl * (complementCoe φ) ⟨ℓ, G'.compl⟩)
      = ∑ G' : FlagWithSize σ ℓ, flagDensity₁ F.2.uncompl G' * φ.coe ⟨ℓ, G'⟩ := by
    apply Finset.sum_congr rfl
    intro G' _
    rw [flagDensity₁_uncompl_compl, complementCoe_apply]
    congr 2
    show FinFlag.uncompl (⟨ℓ, G'.compl⟩ : FinFlag σᶜ) = (⟨ℓ, G'⟩ : FinFlag σ)
    simp only [FinFlag.uncompl, Flag.uncompl_compl]
  rw [hsum]
  exact positiveHom_zeroSpaceProp φ F.uncompl ℓ hℓ

/-- A pair-flag density of `σᶜ`-flags reindexed through `compl`/`uncompl`. -/
theorem flagDensity₂_uncompl_compl {ℓ : ℕ} (F₁ F₂ : FinFlag σᶜ) (G' : FlagWithSize σ ℓ) :
    flagDensity₂ F₁.2 F₂.2 G'.compl = flagDensity₂ F₁.2.uncompl F₂.2.uncompl G' := by
  conv_lhs => rw [← Flag.compl_uncompl F₁.2, ← Flag.compl_uncompl F₂.2]
  rw [flagDensity₂_compl]

theorem complementProfile_mulProp (φ : PositiveHom σ) : mulProp (complementCoe φ) := by
  intro F₁ F₂
  rw [complementCoe_apply, complementCoe_apply]
  rw [sum_flagWithSize_compl
      (fun G => flagDensity₂ F₁.2 F₂.2 G * (complementCoe φ) ⟨F₁.1 + F₂.1 - n₀, G⟩)]
  have hsum : (∑ G' : FlagWithSize σ (F₁.1 + F₂.1 - n₀),
        flagDensity₂ F₁.2 F₂.2 G'.compl * (complementCoe φ) ⟨F₁.1 + F₂.1 - n₀, G'.compl⟩)
      = ∑ G' : FlagWithSize σ (F₁.1 + F₂.1 - n₀),
          flagDensity₂ F₁.2.uncompl F₂.2.uncompl G' * φ.coe ⟨F₁.1 + F₂.1 - n₀, G'⟩ := by
    apply Finset.sum_congr rfl
    intro G' _
    rw [flagDensity₂_uncompl_compl, complementCoe_apply]
    congr 2
    show FinFlag.uncompl (⟨F₁.1 + F₂.1 - n₀, G'.compl⟩ : FinFlag σᶜ)
        = (⟨F₁.1 + F₂.1 - n₀, G'⟩ : FinFlag σ)
    simp only [FinFlag.uncompl, Flag.uncompl_compl]
  -- `F.uncompl.1 = F.1`, so the resulting size matches `mulProp φ.coe`
  rw [hsum]
  -- both sides are `mulProp φ.coe` at `F₁.uncompl, F₂.uncompl` (sizes defeq to `F₁.1, F₂.1`)
  exact positiveHom_mulProp φ F₁.uncompl F₂.uncompl

/-- **The complement of a positive homomorphism.**  Its density profile is `G ↦ φ.coe G.uncompl`. -/
noncomputable def complHom (φ : PositiveHom σ) : PositiveHom σᶜ :=
  positiveHomFromZeroSpaceOneMulProp (complementCoe φ)
    (complementProfile_zeroSpaceProp φ) (complementProfile_oneProp φ)
    (complementProfile_mulProp φ)

@[simp]
theorem complHom_coe (φ : PositiveHom σ) (G : FinFlag σᶜ) :
    (complHom φ).coe G = φ.coe G.uncompl := by
  show linearExtension (complementCoe φ) (basisVector G) = (complementCoe φ) G
  rw [linearExtension_basisVector]

/-! ## C. The symmetric inverse and mutual-inverse laws -/

/-- The un-complement density profile of `η`, packaged in `FlagDensitySpace σ`: each `σ`-flag `F`
is sent to `η.coe F.compl ∈ [0,1]`. -/
noncomputable def uncomplementCoe (η : PositiveHom σᶜ) : FlagDensitySpace σ :=
  { val := fun F => η.coe F.compl
    property := by
      simp only [FlagDensitySpace, Set.pi_univ_Icc, Set.mem_Icc]
      exact ⟨fun F => (flagDensitySpace_mem_Icc_zero_one η.coe F.compl).1,
             fun F => (flagDensitySpace_mem_Icc_zero_one η.coe F.compl).2⟩ }

@[simp]
theorem uncomplementCoe_apply (η : PositiveHom σᶜ) (F : FinFlag σ) :
    (uncomplementCoe η) F = η.coe F.compl := rfl

/-- The unit `σ`-flag complements to the unit `σᶜ`-flag. -/
theorem finFlag_one_compl : (1 : FinFlag σ).compl = (1 : FinFlag σᶜ) := by
  rw [← finFlag_one_uncompl, FinFlag.compl_uncompl]

theorem uncomplementProfile_oneProp (η : PositiveHom σᶜ) : oneProp (uncomplementCoe η) := by
  show (uncomplementCoe η) (1 : FinFlag σ) = 1
  rw [uncomplementCoe_apply, finFlag_one_compl]
  exact positiveHom_oneProp η

theorem flagDensity₁_compl_uncompl {ℓ : ℕ} (F : FinFlag σ) (G' : FlagWithSize σᶜ ℓ) :
    flagDensity₁ F.2 G'.uncompl = flagDensity₁ F.2.compl G' := by
  conv_rhs => rw [← Flag.compl_uncompl G']
  rw [flagDensity₁_compl]

theorem uncomplementProfile_zeroSpaceProp (η : PositiveHom σᶜ) :
    zeroSpaceProp (uncomplementCoe η) := by
  intro F ℓ hℓ
  rw [uncomplementCoe_apply]
  -- reindex the RHS sum over `σ`-flags by un-complementing `σᶜ`-flags
  rw [show (∑ G : FlagWithSize σ ℓ, flagDensity₁ F.2 G * (uncomplementCoe η) ⟨ℓ, G⟩)
        = ∑ G' : FlagWithSize σᶜ ℓ, flagDensity₁ F.2 G'.uncompl * (uncomplementCoe η) ⟨ℓ, G'.uncompl⟩
      from (Equiv.sum_comp (Flag.complEquiv (σ := σ) (ℓ := ℓ)).symm
        (fun G => flagDensity₁ F.2 G * (uncomplementCoe η) ⟨ℓ, G⟩)).symm]
  have hsum : (∑ G' : FlagWithSize σᶜ ℓ,
        flagDensity₁ F.2 G'.uncompl * (uncomplementCoe η) ⟨ℓ, G'.uncompl⟩)
      = ∑ G' : FlagWithSize σᶜ ℓ, flagDensity₁ F.2.compl G' * η.coe ⟨ℓ, G'⟩ := by
    apply Finset.sum_congr rfl
    intro G' _
    rw [flagDensity₁_compl_uncompl, uncomplementCoe_apply]
    congr 2
    show FinFlag.compl (⟨ℓ, G'.uncompl⟩ : FinFlag σ) = (⟨ℓ, G'⟩ : FinFlag σᶜ)
    simp only [FinFlag.compl, Flag.compl_uncompl]
  rw [hsum]
  exact positiveHom_zeroSpaceProp η F.compl ℓ hℓ

theorem flagDensity₂_compl_uncompl {ℓ : ℕ} (F₁ F₂ : FinFlag σ) (G' : FlagWithSize σᶜ ℓ) :
    flagDensity₂ F₁.2 F₂.2 G'.uncompl = flagDensity₂ F₁.2.compl F₂.2.compl G' := by
  conv_rhs => rw [← Flag.compl_uncompl G']
  rw [flagDensity₂_compl]

theorem uncomplementProfile_mulProp (η : PositiveHom σᶜ) : mulProp (uncomplementCoe η) := by
  intro F₁ F₂
  rw [uncomplementCoe_apply, uncomplementCoe_apply]
  rw [show (∑ G : FlagWithSize σ (F₁.1 + F₂.1 - n₀),
        flagDensity₂ F₁.2 F₂.2 G * (uncomplementCoe η) ⟨F₁.1 + F₂.1 - n₀, G⟩)
        = ∑ G' : FlagWithSize σᶜ (F₁.1 + F₂.1 - n₀),
            flagDensity₂ F₁.2 F₂.2 G'.uncompl
              * (uncomplementCoe η) ⟨F₁.1 + F₂.1 - n₀, G'.uncompl⟩
      from (Equiv.sum_comp (Flag.complEquiv (σ := σ) (ℓ := F₁.1 + F₂.1 - n₀)).symm
        (fun G => flagDensity₂ F₁.2 F₂.2 G
          * (uncomplementCoe η) ⟨F₁.1 + F₂.1 - n₀, G⟩)).symm]
  have hsum : (∑ G' : FlagWithSize σᶜ (F₁.1 + F₂.1 - n₀),
        flagDensity₂ F₁.2 F₂.2 G'.uncompl
          * (uncomplementCoe η) ⟨F₁.1 + F₂.1 - n₀, G'.uncompl⟩)
      = ∑ G' : FlagWithSize σᶜ (F₁.1 + F₂.1 - n₀),
          flagDensity₂ F₁.2.compl F₂.2.compl G' * η.coe ⟨F₁.1 + F₂.1 - n₀, G'⟩ := by
    apply Finset.sum_congr rfl
    intro G' _
    rw [flagDensity₂_compl_uncompl, uncomplementCoe_apply]
    congr 2
    show FinFlag.compl (⟨F₁.1 + F₂.1 - n₀, G'.uncompl⟩ : FinFlag σ)
        = (⟨F₁.1 + F₂.1 - n₀, G'⟩ : FinFlag σᶜ)
    simp only [FinFlag.compl, Flag.compl_uncompl]
  rw [hsum]
  exact positiveHom_mulProp η F₁.compl F₂.compl

/-- The symmetric inverse of `complHom`: the un-complement of a positive homomorphism on `σᶜ`. -/
noncomputable def uncomplHom (η : PositiveHom σᶜ) : PositiveHom σ :=
  positiveHomFromZeroSpaceOneMulProp (uncomplementCoe η)
    (uncomplementProfile_zeroSpaceProp η) (uncomplementProfile_oneProp η)
    (uncomplementProfile_mulProp η)

@[simp]
theorem uncomplHom_coe (η : PositiveHom σᶜ) (F : FinFlag σ) :
    (uncomplHom η).coe F = η.coe F.compl := by
  show linearExtension (uncomplementCoe η) (basisVector F) = (uncomplementCoe η) F
  rw [linearExtension_basisVector]

/-- `uncomplHom (complHom φ) = φ`. -/
theorem uncomplHom_complHom (φ : PositiveHom σ) : uncomplHom (complHom φ) = φ := by
  apply PositiveHom.coe_injective
  apply (DFunLike.coe_injective (F := FlagDensitySpace σ))
  funext F
  show (uncomplHom (complHom φ)).coe F = φ.coe F
  rw [uncomplHom_coe, complHom_coe, FinFlag.uncompl_compl]

/-- `complHom (uncomplHom η) = η`. -/
theorem complHom_uncomplHom (η : PositiveHom σᶜ) : complHom (uncomplHom η) = η := by
  apply PositiveHom.coe_injective
  apply (DFunLike.coe_injective (F := FlagDensitySpace σᶜ))
  funext G
  show (complHom (uncomplHom η)).coe G = η.coe G
  rw [complHom_coe, uncomplHom_coe, FinFlag.compl_uncompl]

/-! ## D. The homeomorphism of homomorphism spaces -/

/-- The forward map on homomorphism spaces, as a coordinate identity: the `σᶜ`-coordinate `G` of
the image is the `σ`-coordinate `G.uncompl` of the source. -/
theorem complHomeo_toFun_val (χ : PositiveHomSpace σ) (G : FinFlag σᶜ) :
    (posHomPoint (complHom (PositiveHomSpace.toPosHom χ))).val G = χ.val G.uncompl := by
  rw [posHomPoint_val_apply, ← PositiveHom.coe_flag, complHom_coe, PositiveHom.coe_flag,
    PositiveHomSpace.toPosHom_basisVector]

/-- The inverse map on homomorphism spaces, as a coordinate identity. -/
theorem uncomplHomeo_invFun_val (η : PositiveHomSpace σᶜ) (F : FinFlag σ) :
    (posHomPoint (uncomplHom (PositiveHomSpace.toPosHom η))).val F = η.val F.compl := by
  rw [posHomPoint_val_apply, ← PositiveHom.coe_flag, uncomplHom_coe, PositiveHom.coe_flag,
    PositiveHomSpace.toPosHom_basisVector]

/-- `toPosHom` undoes `posHomPoint`. -/
theorem toPosHom_posHomPoint (φ : PositiveHom σ) :
    PositiveHomSpace.toPosHom (posHomPoint φ) = φ := by
  apply PositiveHom.coe_injective
  apply (DFunLike.coe_injective (F := FlagDensitySpace σ))
  funext F
  show (PositiveHomSpace.toPosHom (posHomPoint φ)).coe F = φ.coe F
  rw [PositiveHom.coe_flag, PositiveHomSpace.toPosHom_basisVector, posHomPoint_val_apply,
    ← PositiveHom.coe_flag]

/-- `posHomPoint` undoes `toPosHom`. -/
theorem posHomPoint_toPosHom (χ : PositiveHomSpace σ) :
    posHomPoint (PositiveHomSpace.toPosHom χ) = χ := by
  apply Subtype.ext
  apply (DFunLike.coe_injective (F := FlagDensitySpace σ))
  funext F
  show (posHomPoint (PositiveHomSpace.toPosHom χ)).val F = χ.val F
  rw [posHomPoint_val_apply, ← PositiveHomSpace.toPosHom_basisVector]

/-- Continuity of the forward map: each coordinate of the image is a single coordinate of the
source, hence continuous. -/
theorem continuous_complHomeo_toFun :
    Continuous (fun χ : PositiveHomSpace σ =>
      posHomPoint (complHom (PositiveHomSpace.toPosHom χ))) := by
  apply Continuous.subtype_mk
  apply continuous_induced_rng.mpr
  rw [continuous_pi_iff]
  intro G
  refine ((FinFlag.continuous G.uncompl).comp continuous_subtype_val).congr ?_
  intro χ
  exact (complHomeo_toFun_val χ G).symm

/-- Continuity of the inverse map. -/
theorem continuous_complHomeo_invFun :
    Continuous (fun η : PositiveHomSpace σᶜ =>
      posHomPoint (uncomplHom (PositiveHomSpace.toPosHom η))) := by
  apply Continuous.subtype_mk
  apply continuous_induced_rng.mpr
  rw [continuous_pi_iff]
  intro F
  refine ((FinFlag.continuous F.compl).comp continuous_subtype_val).congr ?_
  intro η
  exact (uncomplHomeo_invFun_val η F).symm

/-- **Complementation is a homeomorphism of homomorphism spaces.**  It sends `χ` to the point whose
`σᶜ`-coordinate `G` is the `σ`-coordinate `G.uncompl` of `χ`. -/
noncomputable def complHomeo : PositiveHomSpace σ ≃ₜ PositiveHomSpace σᶜ where
  toFun χ := posHomPoint (complHom (PositiveHomSpace.toPosHom χ))
  invFun η := posHomPoint (uncomplHom (PositiveHomSpace.toPosHom η))
  left_inv χ := by
    show posHomPoint (uncomplHom (PositiveHomSpace.toPosHom
      (posHomPoint (complHom (PositiveHomSpace.toPosHom χ))))) = χ
    rw [toPosHom_posHomPoint, uncomplHom_complHom, posHomPoint_toPosHom]
  right_inv η := by
    show posHomPoint (complHom (PositiveHomSpace.toPosHom
      (posHomPoint (uncomplHom (PositiveHomSpace.toPosHom η))))) = η
    rw [toPosHom_posHomPoint, complHom_uncomplHom, posHomPoint_toPosHom]
  continuous_toFun := continuous_complHomeo_toFun
  continuous_invFun := continuous_complHomeo_invFun

@[simp]
theorem complHomeo_val (χ : PositiveHomSpace σ) (G : FinFlag σᶜ) :
    (complHomeo χ).val G = χ.val G.uncompl :=
  complHomeo_toFun_val χ G

@[simp]
theorem complHomeo_symm_val (η : PositiveHomSpace σᶜ) (F : FinFlag σ) :
    ((complHomeo (σ := σ)).symm η).val F = η.val F.compl :=
  uncomplHomeo_invFun_val η F

/-- The forward homeomorphism, applied to an evaluation at `⟦basisVector G⟧`. -/
theorem complHomeo_apply_eval (χ : PositiveHomSpace σ) (G : FinFlag σᶜ) :
    (PositiveHomSpace.toPosHom (complHomeo χ)) ⟦basisVector G⟧ = χ.val G.uncompl := by
  rw [PositiveHomSpace.toPosHom_basisVector, complHomeo_val]

end MetaTheory

end FlagAlgebras
