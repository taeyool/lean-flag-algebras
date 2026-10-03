-- Counts the constants each certificate file adds to the Lean environment
-- (input to papers/AFM/artifact_appendix.py, saved as artifact_counts.txt).
-- Run from a built checkout of the release repository:
--   lake env lean <path>/papers/AFM/checks/CountGen.lean
import LeanFlagAlgebras

open Lean Elab Command

/-- For each listed module, count the non-internal constants it declares:
source declarations plus everything the generation commands emit. -/
elab "#count_module_decls " ids:ident+ : command => do
  let env ← getEnv
  for id in ids do
    let modName := id.getId
    match env.getModuleIdx? modName with
    | none => logWarning m!"MODULE NOT FOUND: {modName}"
    | some idx =>
      let n := env.constants.fold (init := (0 : Nat)) fun acc c _ =>
        if !c.isInternal && env.getModuleIdxFor? c == some idx then acc + 1 else acc
      logInfo m!"MODDECLS {modName} {n}"

/-- Count all non-internal constants declared in modules whose name starts
with the given prefix. -/
elab "#count_prefix_decls " ids:ident+ : command => do
  let env ← getEnv
  for id in ids do
    let pfx := id.getId
    let mods := env.header.moduleNames
    let n := env.constants.fold (init := (0 : Nat)) fun acc c _ =>
      match env.getModuleIdxFor? c with
      | some idx =>
        if !c.isInternal && pfx.isPrefixOf mods[idx.toNat]! then acc + 1 else acc
      | none => acc
    logInfo m!"PREFIXDECLS {pfx} {n}"

#count_module_decls
  LeanFlagAlgebras.Flagmatic.Mantel LeanFlagAlgebras.Flagmatic.K3freeP3
  LeanFlagAlgebras.Flagmatic.K3freeC4 LeanFlagAlgebras.Flagmatic.K4freeEdge
  LeanFlagAlgebras.Flagmatic.ErdosPentagon LeanFlagAlgebras.Flagmatic.K5freeEdge
  LeanFlagAlgebras.Flagmatic.C5freeEdge

#count_prefix_decls LeanFlagAlgebras
