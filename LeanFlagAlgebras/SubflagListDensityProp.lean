import «LeanFlagAlgebras».FlagDef
import «LeanFlagAlgebras».SubflagListDensity

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic

open FlagAlgebras
open LabeledSubgraph
open Classical
open MeasureTheory ProbabilityTheory
noncomputable section

variable {T : Type} [Fintype T] [DecidableEq T]
variable {V : Type} [Fintype V] [DecidableEq V]
variable {W : Type} [Fintype W] [DecidableEq W]
variable {U : Type} [Fintype U] [DecidableEq U]

variable {σ : FlagType T} {t : ℕ}
variable {Vl  : Fin t → Type} [FintypeList Vl]  [DecidableEqList Vl]
variable {Fl : FlagList σ t Vl}

def SampleSpace (_ : LabeledGraph σ V) (k : ℕ) : Type := {S: Finset V // S.card = k}
instance : Fintype (SampleSpace G k) := sorry
instance : MeasurableSpace (SampleSpace G k) := sorry

def uniformMeasure [Nonempty (SampleSpace G k)] : Measure (SampleSpace G k) :=
  (PMF.uniformOfFintype (SampleSpace G k)).toMeasure

def event_isomorphic (F₀ : LabeledGraph σ W) (G : LabeledGraph σ V) : Set (SampleSpace G F₀.size) :=
  let p (S : SampleSpace G F₀.size) (h : G.type_verts ⊆ S.val) : Prop :=
    Nonempty (F₀ ≃f (inducedLabeledSubgraph G S.val h).coe)
  { S | ∃ h : G.type_verts ⊆ S.val, p S h}

def p (F₀ : LabeledGraph σ W) (G : LabeledGraph σ U) [Nonempty (SampleSpace G F₀.size)] : Real :=
  (uniformMeasure (event_isomorphic F₀ G)).toReal

theorem p_definitionaly_eq (F : LabeledGraph σ W) (G : LabeledGraph σ V) [Nonempty (SampleSpace G F.size)] :
  p F G = labeledSubgraphDensity F G := by
  dsimp [p, event_isomorphic, uniformMeasure]
  dsimp [labeledSubgraphDensity, labeledSubgraphCount]
  sorry

/- Lemma 2.3 -/

theorem flagListDensity_prod_approx
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : ∃ k , abs (flagListDensity Fl G - ∏ i in Finset.univ, flagDensity₁ (Fl i) G ) ≤ (∑ i in Finset.univ, (Fl i).out.size ) ^ k / G.out.size
  := by
  sorry

theorem flagListDensity_prod_approx'
    (F : Flag σ U) (G : Flag σ W)
    : ∃ k , abs (flagDensity₂ F F G - flagDensity₁ F G * flagDensity₁ F G ) ≤ (2 * F.out.size) ^ k / G.out.size
  := by
  use 2
  sorry

theorem subflagListDensity_ge_0
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : 0 ≤ flagListDensity Fl G := by
  sorry

theorem subflagListDensity_le_1
    (Fl : FlagList σ t Vl) (G : Flag σ W)
    : flagListDensity Fl G ≤ 1 := by
  sorry
