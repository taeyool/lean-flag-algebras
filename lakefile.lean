-- Lake build configuration: declares the `lean-flag-algebras` package, pins the
-- mathlib dependency (v4.27.0), and sets the `LeanFlagAlgebras` library (root
-- import manifest `LeanFlagAlgebras.lean`) as the default build target.
import Lake
open Lake DSL

package «lean-flag-algebras» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

@[default_target]
lean_lib «LeanFlagAlgebras» where
  -- Build the root import manifest and every module tree EXCEPT `Archive/`
  -- (retired experiments, kept for reference but excluded from the build).
  globs := #[
    .one `LeanFlagAlgebras,
    .submodules `LeanFlagAlgebras.Automation,
    .submodules `LeanFlagAlgebras.Differential,
    .submodules `LeanFlagAlgebras.ErdosPentagon,
    .submodules `LeanFlagAlgebras.FlagAlgebra,
    .submodules `LeanFlagAlgebras.Flagmatic,
    .submodules `LeanFlagAlgebras.Flags,
    .submodules `LeanFlagAlgebras.Forbid,
    .submodules `LeanFlagAlgebras.GraphAlgebra,
    .submodules `LeanFlagAlgebras.Logic,
    .submodules `LeanFlagAlgebras.MantelTheorem,
    .andSubmodules `LeanFlagAlgebras.MetaTheory,
    .submodules `LeanFlagAlgebras.Turan,
    .submodules `LeanFlagAlgebras.Utils
  ]
