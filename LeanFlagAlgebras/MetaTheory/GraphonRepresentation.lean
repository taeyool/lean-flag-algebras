import LeanFlagAlgebras.MetaTheory.GraphonKernelTransport
import LeanFlagAlgebras.MetaTheory.GraphonCounting

/-! # The paper-verbatim tripartite theorem

The paper's `thm:k4free-p4-tripartite` (Thm 102), stated in its own quantifier shape: over
graphons representing a point of the slice, rather than over the slice's points directly.

* `posHomPoint_eq_of_graphonProfileFun_eq` — a graphon whose profile agrees with `φ₀`'s
  carries the same point of `X_∅`.
* `k4free_p4_tripartite_of_represents` — **the unconditional paper-verbatim Thm 102**:
  *every* graphon representing a point of the `K₄`-free `P₄`-slice (with both root types of
  positive mass) is a.e. the balanced complete tripartite graphon. This is the paper's own
  "let `W` represent a point of `Y_{P4}`; then `W` is a.e. …" — and it needs **no**
  representation-existence input, because the quantifier runs over the representatives.
* `k4free_p4_tripartite_of_rep_exists` — the existence form, conditional on the one named
  classical input `hrep : ∀ φ₀, ∃ W, ∀ F, graphonProfileFun W F = φ₀.coe F` (Lovász–Szegedy
  existence, in the standing named-hypothesis convention of `hES`/`hZykov`). The graphon-hom
  range is already proved **dense** in `X_∅` (`exists_graphonHomPoint_seq_tendsto`), so `hrep`
  is equivalent to `IsClosed (Set.range graphonHomPoint)`.

Cor 106 does not yet admit the same treatment: `Graphon.slice_rigidity` has no
rooted-transport counterpart. These theorems consume `k4freeP4_graphon_tripartite`.
-/

open MeasureTheory unitInterval
open scoped Classical

namespace FlagAlgebras.MetaTheory

open FlagAlgebras
open CompleteGraphFreeP4

/-- Profile agreement gives point agreement: a graphon representing `φ₀` carries the same
point of `X_∅`. -/
theorem posHomPoint_eq_of_graphonProfileFun_eq {W : Graphon} {φ₀ : PositiveHom ∅ₜ}
    (hW : ∀ F : FinFlag ∅ₜ, graphonProfileFun W F = φ₀.coe F) :
    posHomPoint (graphonHom W) = posHomPoint φ₀ := by
  apply Subtype.ext
  apply DFunLike.ext
  intro F
  rw [posHomPoint_val_apply, posHomPoint_val_apply, ← PositiveHom.coe_flag,
    ← PositiveHom.coe_flag, graphonHom_coe]
  exact hW F

/-- The value of `⟨σ'⟩₀` transports along profile agreement: a graphon-hom value on the
type-flag class is exactly the profile value, so `hW` identifies `φ_W ⟨σ'⟩₀` with
`φ₀ ⟨σ'⟩₀` (the same idiom as `GraphonRootedMeasure.rootMass_eq_typeFlag`). -/
private lemma graphonHom_typeFlag_eq_of_graphonProfileFun_eq {W : Graphon} {φ₀ : PositiveHom ∅ₜ}
    (hW : ∀ F : FinFlag ∅ₜ, graphonProfileFun W F = φ₀.coe F) (σ' : FlagType (Fin 2)) :
    (graphonHom W) ⟨σ'⟩₀ = φ₀ ⟨σ'⟩₀ := by
  show (graphonHom W).coe _ = φ₀.coe _
  rw [graphonHom_coe]
  exact hW _

/-- **The paper-verbatim Thm 102 (`thm:k4free-p4-tripartite`), unconditionally**: every
graphon representing a point of the `K₄`-free `P₄`-slice — with both root types of positive
mass — is almost everywhere the balanced complete tripartite graphon. -/
theorem k4free_p4_tripartite_of_represents {W : Graphon} {φ₀ : PositiveHom ∅ₜ}
    (hW : ∀ F : FinFlag ∅ₜ, graphonProfileFun W F = φ₀.coe F)
    (hστ : φ₀ ⟨FlagType_2_1⟩₀ > 0) (hση : φ₀ ⟨FlagType_2_0⟩₀ > 0)
    (hmem : posHomPoint φ₀ ∈ k4freeP4Slice) :
    ∃ P : I → Fin 3, Measurable P
      ∧ (∀ i, volume (P ⁻¹' {i}) = ENNReal.ofReal (1 / 3))
      ∧ ∀ᵐ z : I × I, W.W z.1 z.2 = if P z.1 = P z.2 then 0 else 1 := by
  have hpt := posHomPoint_eq_of_graphonProfileFun_eq hW
  refine k4freeP4_graphon_tripartite W ?_ ?_ ?_
  · rw [graphonHom_typeFlag_eq_of_graphonProfileFun_eq hW]
    exact hστ
  · rw [graphonHom_typeFlag_eq_of_graphonProfileFun_eq hW]
    exact hση
  · rw [hpt]
    exact hmem

/-- The existence form of Thm 102, conditional on the one named classical input
(Lovász–Szegedy existence, `hrep`): every point of the slice (with both root types of
positive mass) is represented by some graphon, and any such representative is a.e. the
balanced complete tripartite graphon. -/
theorem k4free_p4_tripartite_of_rep_exists
    (hrep : ∀ φ₀ : PositiveHom ∅ₜ, ∃ W : Graphon,
        ∀ F : FinFlag ∅ₜ, graphonProfileFun W F = φ₀.coe F)
    {φ₀ : PositiveHom ∅ₜ}
    (hστ : φ₀ ⟨FlagType_2_1⟩₀ > 0) (hση : φ₀ ⟨FlagType_2_0⟩₀ > 0)
    (hmem : posHomPoint φ₀ ∈ k4freeP4Slice) :
    ∃ W : Graphon, (∀ F : FinFlag ∅ₜ, graphonProfileFun W F = φ₀.coe F)
      ∧ ∃ P : I → Fin 3, Measurable P
          ∧ (∀ i, volume (P ⁻¹' {i}) = ENNReal.ofReal (1 / 3))
          ∧ ∀ᵐ z : I × I, W.W z.1 z.2 = if P z.1 = P z.2 then 0 else 1 := by
  obtain ⟨W, hW⟩ := hrep φ₀
  exact ⟨W, hW, k4free_p4_tripartite_of_represents hW hστ hση hmem⟩

end FlagAlgebras.MetaTheory
