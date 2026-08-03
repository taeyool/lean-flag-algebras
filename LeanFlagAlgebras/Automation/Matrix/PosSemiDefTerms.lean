import LeanFlagAlgebras.Automation.Matrix.PosSemiDef

/-! # `psd_real_ldlt` for inline literals

The `psd_real_ldlt` tactic of `PosSemiDef.lean` takes the matrix, `L`-factor, and
diagonal as *identifiers* of file-level `def`s (its `norm_num [$d]` branch unfolds the
diagonal by name).  The `flag_certificate` tactic instead pastes the certificate data
into the proof as literals, so it needs a variant that accepts arbitrary terms.  This
lives in its own file so that adding it does not invalidate the (expensive) compiled
examples that import `PosSemiDef.lean`. -/

/-- Term-argument variant of `psd_real_ldlt`, for inline matrix/vector *literals* (as
synthesized by the `flag_certificate` tactic).  Both side goals of
`posSemidef_real_of_LDLt` — `0 ≤ d` and the factorization equality — are closed by
kernel evaluation, which reduces closed literals directly. -/
syntax (name := psdRealLdltTerms)
  "psd_real_ldlt_terms" ppSpace term:max ppSpace term:max ppSpace term:max : tactic

macro_rules
  | `(tactic| psd_real_ldlt_terms $M:term $L:term $d:term) =>
    `(tactic|
        refine posSemidef_real_of_LDLt (M := $M) (L := $L) (d := $d) ?_ ?_ <;>
          decide +kernel)
