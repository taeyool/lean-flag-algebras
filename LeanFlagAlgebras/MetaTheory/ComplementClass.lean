module

public import LeanFlagAlgebras.MetaTheory.ComplementHom
public import LeanFlagAlgebras.MetaTheory.HeredClass
public import LeanFlagAlgebras.MetaTheory.ConstrainedClass

@[expose] public section

/-! # Complementation transfers the constrained quotient space (paper `lem:complementation`, Layer 3)

Layers 1–2 (`MetaTheory/FlagComplement.lean`, `MetaTheory/ComplementHom.lean`) build the
complement homeomorphism `complHomeo : PositiveHomSpace σ ≃ₜ PositiveHomSpace σᶜ` acting by
`(complHomeo χ).val G = χ.val G.uncompl`.  This file is **Layer 3**: it complements a *hereditary
graph class* and shows that `complHomeo` carries the constrained quotient space `Q_σ(K)` exactly
onto `Q_{σᶜ}(K̄)`.

* **The complement class.**  `HeredClass.compl hc` is `K̄ = {Ḡ : G ∈ K}` — again hereditary,
  because an induced embedding `H ↪g G` complements to `Hᶜ ↪g Gᶜ` (`complEmbedding`), exactly the
  pattern used for `coC4FreeClass` in `MetaTheory/DenseObstruction.lean`.
* **The forbidden-flag bridge.**  `complClass_forbσ_iff` says a `σᶜ`-flag `G` is forbidden by the
  complement class iff its un-complement `G.uncompl` is forbidden by the original class.  This is
  the load-bearing combinatorial identity: it reduces to
  `(hc.compl).underlyingMem (unlabel G.2) ↔ hc.underlyingMem (unlabel G.uncompl.2)`, both sides of
  which compute to `hc.Mem (Grepᶜ)` after picking a representative.
* **The `Q_σ` transfer (the deliverable).**  `complHomeo_mem_Qσ_iff` transports membership in the
  constrained space across `complHomeo`, and `complHomeo_image_Qσ` upgrades this to the set
  equality `complHomeo '' Q_σ(K) = Q_{σᶜ}(K̄)`.  The mathematical content is the bridge applied
  through the bijection `F ↦ F.compl` (inverse `G ↦ G.uncompl`).
-/

namespace FlagAlgebras.MetaTheory

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-! ## A. The complement hereditary class -/

/-- **The complement of a hereditary graph class.**  `K̄ = {Ḡ : G ∈ K}`, i.e. a graph `G` is in
`hc.compl` iff its complement `Gᶜ` is in `hc`.  Again hereditary: an induced embedding `H ↪g G`
complements to an induced embedding `Hᶜ ↪g Gᶜ` (`complEmbedding`), so heredity of `hc` at `Gᶜ`
transports to heredity of `hc.compl` at `G`.  (Mirrors `coC4FreeClass` in
`MetaTheory/DenseObstruction.lean`.) -/
def HeredClass.compl (hc : HeredClass) : HeredClass where
  Mem {_V} _ _ G := hc.Mem Gᶜ
  comap {_V _W} _ _ _ _ {_G} {_H} e hG := hc.comap (complEmbedding e) hG

/-- Membership in `hc.compl` is membership of the complement in `hc`, definitionally. -/
@[simp]
theorem HeredClass.compl_Mem (hc : HeredClass) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : (hc.compl).Mem G ↔ hc.Mem Gᶜ := Iff.rfl

/-! ## B. The forbidden-flag correspondence -/

/-- **The forbidden-flag bridge.**  A `σᶜ`-flag `G` is forbidden by the complement class iff its
un-complement `G.uncompl` is forbidden by the original class.  Both sides unfold to a negated
underlying-membership; choosing a representative `⟦Grep⟧` of `G.2`, each side computes to
`¬ hc.Mem (Grep.graphᶜ)`, so the equivalence is definitional. -/
theorem complClass_forbσ_iff (hc : HeredClass) (σ : FlagType (Fin n₀)) (G : FinFlag σᶜ) :
    ((hc.compl).constraintOf σᶜ).forbσ G ↔ (hc.constraintOf σ).forbσ G.uncompl := by
  show ¬ (hc.compl).underlyingMem (unlabel G.2) ↔ ¬ hc.underlyingMem (unlabel G.uncompl.2)
  -- reduce `G.2` to a representative `⟦Grep⟧`
  rcases Quotient.exists_rep G.2 with ⟨Grep, hGrep⟩
  have hG2 : G.2 = (⟦Grep⟧ : Flag σᶜ (Fin G.1)) := hGrep.symm
  have huncompl : G.uncompl.2 = (⟦Grep.uncompl⟧ : Flag σ (Fin G.1)) := by
    show G.2.uncompl = _
    rw [hG2, Flag.uncompl_mk]
  rw [hG2, huncompl]
  -- left:  `(hc.compl).underlyingMem (unlabel ⟦Grep⟧) = (hc.compl).Mem Grep.graph = hc.Mem Grep.graphᶜ`
  rw [hc.compl.underlyingMem_unlabel_mk Grep, hc.compl_Mem]
  -- right: `hc.underlyingMem (unlabel ⟦Grep.uncompl⟧) = hc.Mem Grep.uncompl.graph = hc.Mem Grep.graphᶜ`
  rw [hc.underlyingMem_unlabel_mk Grep.uncompl, LabeledGraph.uncompl_graph]

/-- The mirror of `complClass_forbσ_iff`: a `σ`-flag `F` is forbidden by `hc` iff its complement
`F.compl` is forbidden by `hc.compl`.  Obtained from the bridge at `F.compl` via the round-trip
`F.compl.uncompl = F`. -/
theorem complClass_forbσ_iff' (hc : HeredClass) (σ : FlagType (Fin n₀)) (F : FinFlag σ) :
    ((hc.compl).constraintOf σᶜ).forbσ F.compl ↔ (hc.constraintOf σ).forbσ F := by
  rw [complClass_forbσ_iff hc σ F.compl, FinFlag.uncompl_compl]

/-! ## C. Transfer of the constrained quotient space `Q_σ` -/

/-- **Membership transfer.**  `complHomeo χ` lies in the constrained space of the complement class
iff `χ` lies in the constrained space of the original class.  Rewriting both sides with
`mem_Qσ_iff` and `complHomeo_val`, the complement-class condition reindexes along the bijection
`F ↦ F.compl` / `G ↦ G.uncompl` to the original-class condition (via `complClass_forbσ_iff`). -/
theorem complHomeo_mem_Qσ_iff (hc : HeredClass) (σ : FlagType (Fin n₀)) (χ : PositiveHomSpace σ) :
    complHomeo χ ∈ Qσ ((hc.compl).constraintOf σᶜ).forbσ ↔ χ ∈ Qσ (hc.constraintOf σ).forbσ := by
  rw [mem_Qσ_iff, mem_Qσ_iff]
  constructor
  · -- LHS → RHS: for `F : FinFlag σ`, instantiate the LHS at `G := F.compl`.
    intro hLHS F hF
    have hForb : ((hc.compl).constraintOf σᶜ).forbσ F.compl :=
      (complClass_forbσ_iff' hc σ F).mpr hF
    have h := hLHS F.compl hForb
    rwa [complHomeo_val, FinFlag.uncompl_compl] at h
  · -- RHS → LHS: for `G : FinFlag σᶜ`, instantiate the RHS at `F := G.uncompl`.
    intro hRHS G hG
    rw [complHomeo_val]
    exact hRHS G.uncompl ((complClass_forbσ_iff hc σ G).mp hG)

/-- **The set equality (the deliverable).**  `complHomeo` carries the constrained quotient space of
`hc` exactly onto that of `hc.compl`: `complHomeo '' Q_σ(K) = Q_{σᶜ}(K̄)`.  Both inclusions are
`complHomeo_mem_Qσ_iff` applied through the `complHomeo` bijection. -/
theorem complHomeo_image_Qσ (hc : HeredClass) (σ : FlagType (Fin n₀)) :
    complHomeo '' (Qσ (hc.constraintOf σ).forbσ) = Qσ ((hc.compl).constraintOf σᶜ).forbσ := by
  ext η
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    exact (complHomeo_mem_Qσ_iff hc σ χ).mpr hχ
  · intro hη
    refine ⟨complHomeo.symm η, ?_, complHomeo.apply_symm_apply η⟩
    apply (complHomeo_mem_Qσ_iff hc σ (complHomeo.symm η)).mp
    rwa [complHomeo.apply_symm_apply η]

end FlagAlgebras.MetaTheory
