-- Prints the axioms of every declaration in the paper's statement-to-declaration
-- table, the seven *_flagAlgebra theorems and the README's meta-theory headline
-- theorems, and counts the generated pair-density lemmas (Appendix A).
-- Run from a built checkout of the release repository:
--   lake env lean <path>/papers/AFM/checks/AxCheck.lean
-- axioms_v1.0.txt is its output at the tag v1.0.
import LeanFlagAlgebras.Flagmatic.Mantel
import LeanFlagAlgebras.Flagmatic.K3freeP3
import LeanFlagAlgebras.Flagmatic.K3freeC4
import LeanFlagAlgebras.Flagmatic.K4freeEdge
import LeanFlagAlgebras.Flagmatic.ErdosPentagon
import LeanFlagAlgebras.Flagmatic.K5freeEdge
import LeanFlagAlgebras.Flagmatic.C5freeEdge
import LeanFlagAlgebras.MantelTheorem.MantelTheorem
import LeanFlagAlgebras.MantelTheorem.GoodmanBound
import LeanFlagAlgebras.MantelTheorem.GoodmanRamsey
import LeanFlagAlgebras.ErdosPentagon.ErdosPentagon
import LeanFlagAlgebras.MetaTheory.SupportClosure
import LeanFlagAlgebras.MetaTheory.BlowupClosed
import LeanFlagAlgebras.MetaTheory.EmptyTypeCollapse
import LeanFlagAlgebras.MetaTheory.C4Free
import LeanFlagAlgebras.MetaTheory.CloneClosed
import LeanFlagAlgebras.MetaTheory.RelativePositivstellensatz
import LeanFlagAlgebras.MetaTheory.C5EdgeObstruction
import LeanFlagAlgebras.FlagAlgebra.SubflagListDensity
import LeanFlagAlgebras.FlagAlgebra.FlagAlgebra
import LeanFlagAlgebras.FlagAlgebra.FlagSequence
import LeanFlagAlgebras.FlagAlgebra.RandomHom
import LeanFlagAlgebras.FlagAlgebra.Compute.FlagDensity
import LeanFlagAlgebras.FlagAlgebra.Compute.Downward
import LeanFlagAlgebras.Turan.GeneralizedTuran
import LeanFlagAlgebras.Forbid.TuranDensity
import LeanFlagAlgebras.Forbid.Basic
import LeanFlagAlgebras.Automation.Matrix.PosSemiDef
import LeanFlagAlgebras.Automation.Basic

open Lean Elab Command

/-- Print the axioms of every non-internal constant whose last name component
is the given simple name (so namespaces need not be known in advance). -/
elab "#axioms_of " ids:ident+ : command => do
  let env ← getEnv
  for id in ids do
    let target := match id.getId with
      | .str _ s => s
      | n => n.toString
    let hits := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
      match n with
      | .str _ s => if s == target && !n.isInternal then acc.push n else acc
      | _ => acc
    if hits.isEmpty then
      logWarning m!"NOT FOUND: {target}"
    for n in hits.qsort (fun a b => a.toString < b.toString) do
      let axs ← collectAxioms n
      let axs := axs.qsort (fun a b => a.toString < b.toString)
      logInfo m!"AXIOMS {n} : {axs.toList}"

/-- Count the generated pair-density theorems (`flagDensity₂_*`) and shared
subset-pair key theorems (`pairKeys_*`) declared directly in a namespace. -/
elab "#count_generated " ids:ident+ : command => do
  let env ← getEnv
  for id in ids do
    let ns := id.getId
    let (a, b) := env.constants.fold (init := ((0 : Nat), (0 : Nat)))
      fun (acc : Nat × Nat) n _ =>
        match n with
        | .str p s =>
          if p == ns then
            if s.startsWith "flagDensity₂_" then (acc.1 + 1, acc.2)
            else if s.startsWith "pairKeys_" then (acc.1, acc.2 + 1)
            else acc
          else acc
        | _ => acc
    logInfo m!"COUNT {ns} flagDensity₂={a} pairKeys={b}"

-- The seven certificate bounds, in both forms.
#axioms_of Mantel_flagAlgebra K3freeP3_flagAlgebra K3freeC4_flagAlgebra
  K4freeEdge_flagAlgebra ErdosPentagon_flagAlgebra K5freeEdge_flagAlgebra
  C5freeEdge_flagAlgebra
#axioms_of Mantel_turanDensity K3freeP3_turanDensity K3freeC4_turanDensity
  K4freeEdge_turanDensity ErdosPentagon_turanDensity K5freeEdge_turanDensity
  C5freeEdge_turanDensity

-- The density theorems of Sec. 6.
#axioms_of Mantel_Turan ErdosPentagon_Turan ErdosPentagon_Turan_lowerBound
  Goodman_bound_on_triangle_density Goodman_theorem_on_Ramsey_multiplicity

-- The meta-theory headline theorems of Sec. 8.
#axioms_of quotient_implies_ensemble support_criterion blowupClosed_root_plantable
  heredClass_emptyType_rootPlantable c4free_not_rootPlantable
#axioms_of clone_root_plantable relative_positivstellensatz c5free_edge_not_rootPlantable

-- The remaining entries of the statement-to-declaration table.
#axioms_of flagDensity_eq_sum_density_prods flagMulWithSize_indep_on_size
  flagSeq_limit_mem_positiveHom positiveHom_as_flagSeq_limit
  exists_probMeasure_extend_emptyType_positiveHom downward_preserve_semanticCone
  Cauchy_Schwarz_inequality Cauchy_Schwarz_inequality_unit
  tendsto_generalizedTuranDensity generalizedTuranDensity_le_of_forbidLE
  flagDensity₁_eq_sym2FlagDensity₁ flagDensity₂_eq_sym2FlagDensity₂
  downwardNormalizingFactor_eq posSemidef_real_of_LDLt
  forbidLEWith_add_QuadraticForm flagDensity_permute downward_forbidLEWith_nonneg

-- Generated-lemma counts for the "Lemmas" column of Appendix A.
#count_generated Mantel K3freeP3 K3freeC4 K4freeEdge ErdosPentagon K5freeEdge C5freeEdge
