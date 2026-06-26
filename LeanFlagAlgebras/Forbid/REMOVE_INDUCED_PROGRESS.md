# Option B — remove the induced-forbid framework (WIP progress)

Status checkpoint. This refactor replaces the **induced** forbid framework
(`inducedForbidLE` / `inducedForbidEq`, notation `≤ᵢ[F]` / `=ᵢ[F]`, single forbidden
flag) with the **ordinary** framework (`forbidLE` / `forbidEq`, notation `≤[H]` / `=[H]`,
`H : SimpleGraph`, built on the condition-generic `forbidLEWith C` / `forbidEqWith C`
layer) throughout the Flagmatic examples, and aims to delete the induced framework.

**Motivation:** the earlier benchmark showed the induced framework gives **no meaningful
compile-time advantage** (compile time is dominated by framework-neutral `native_decide`
density/multiplication tables + PSD checks; the forbid relation is only an index on the
small SOS-chain proof). So we consolidate on the mathematically-correct ordinary framework.

## Branch

This WIP is committed on branch **`option-b-remove-induced`** (NOT `main`, because the
full build is not yet green — see "not build-verified" below). `main` is unchanged and
still builds.

## DONE and verified green (built as individual targets)

Infrastructure (all additive / non-breaking ports of the induced versions):

- **`Forbid/Basic.lean`** — condition-generic relation-algebra lemmas:
  `forbidLEWith_add_right/_add_left`, `forbidEqWith_add_right`,
  `forbidLEWith_move_add_left_iff`, `forbidLEWith_move_term_left_iff`,
  `forbidEqWith_move_term_left_iff/_move_term_left`, `forbidLEWith_rw_left`,
  `forbidLEWith_rw_left_add_right`, `forbidLEWith_trans_forbidEqWith_right`,
  `downward_forbidEqWith_zero`, `downward_forbidEqWith_equal_flags`; plus the **ordinary
  expansions** `basisVector_quot_forbidEq_sum_ofMem` and
  `basisVector_quot_mul_forbidEq_sum_ofMem`.
- **`API/Basic.lean`** — `forbidLEWith_add_QuadraticForm` (ordinary SOS stacker),
  `one_forbidEq_forbidExpand_one_ofMem` (ordinary unit expansion).
- **`Forbid/CommonGraphs.lean`** — `completeSym2Graph_finFlag_mem_forbiddenFlags r`
  (the clique membership fact `⟨_, toFlag ⟦completeSym2Graph r⟧⟩ ∈ forbiddenFlags (completeGraph (Fin r))`).
- **`API/FlagMulReduce.lean`** — `reduce_downward_flagmul` generalized: it now rewrites
  with the generic `forbidLEWith_*` / `forbidEqWith_*` lemmas, so it drives any
  `forbidLEWith C` goal (ordinary examples turn the `≤[H]` goal into a `forbidLEWith`
  goal via `apply forbidLEWith_trans` etc. before reaching it).
- **`API/FlagExpand.lean`** — `flag_expand_hfree` ported to the ordinary framework and
  made **general in the forbidden graph**: new syntax `flag_expand_hfree N F hmem`
  (`F` = Sym2 forbid ident, `hmem` = membership term `Fflag ∈ forbiddenFlags H`).
- **`Flags/Densities/MulThmGenerator.lean`** — `generate_pruned_forbid_free_mul_theorems`
  ported to emit `=[H]` theorems and made **general in the forbidden graph**: new syntax
  `generate_pruned_forbid_free_mul_theorems patN hostN k m F Hg hmem`
  (`Hg` = forbidden `SimpleGraph`, `hmem` = membership term). **No clique size `r`** — it
  works for any forbidden graph given the matching `Hg` + membership.
- **`Flagmatic/Mantel.lean`** — fully migrated to ordinary and built green end-to-end.
  This is the canonical template for the remaining examples.

## DONE but NOT build-verified

The other 7 Flagmatic examples were migrated by the mechanical pattern below (each by a
subagent; each reported **zero `inducedForbid` code references** remaining — only harmless
doc-comment mentions of `basisVector_quot_inducedForbidEq_sum` in MantelHfree/K4turan/K5turan):

- `Flagmatic/MantelHfree.lean`, `K3forbidP3.lean`, `K3forbidC4.lean`, `K3forbidC6.lean`
  (all forbid K₃), `K4turan.lean` (K₄), `K5turan.lean` (K₅), `ErdosPentagon.lean` (K₃).

**They have NOT been compiled.** The next step is to build them and fix any slips.

## The migration pattern (validated on Mantel)

For an example forbidding clique `Kᵣ` (= `completeSym2Graph r`), with `Fflag :=
(⟨_, Sym2EmptyTypedFlag.toFlag ⟦Kᵣ⟧⟩ : FinFlag ∅ₜ)`:

1. Each `generate_pruned_forbid_free_mul_theorems … Kᵣ` → append
   ` (completeGraph (Fin r)) (completeSym2Graph_finFlag_mem_forbiddenFlags r)`.
   (Leave `…empty_typed_flags`, `…forbid_free_flags`, `…flag_pair_density_theorems` alone.)
2. `=ᵢ[Fflag]` → `=[completeGraph (Fin r)]`; `≤ᵢ[Fflag]` → `≤[completeGraph (Fin r)]`.
3. `flag_expand_hfree N Kᵣ` → `flag_expand_hfree N Kᵣ (completeSym2Graph_finFlag_mem_forbiddenFlags r)`.
4. Delete the proof preamble `apply inducedForbidLE_toFinFlag_imp_forbidLE` +
   `rw [show (completeGraph (Fin r)).toFinFlag = Fflag from (completeSym2Graph_finFlag_eq r).symm]`.
5. `inducedForbidLE_refl Fflag X` → `forbidLEWith_refl _ X`.
6. `one_inducedForbidEq_forbidExpand_one Fflag N` →
   `one_forbidEq_forbidExpand_one_ofMem Fflag (completeSym2Graph_finFlag_mem_forbiddenFlags r) N`.
7. Name swaps (do the longer name before its prefix):
   `inducedForbidLE_trans_inducedForbidEq_right`→`forbidLEWith_trans_forbidEqWith_right`,
   `inducedForbidLE_add_QuadraticForm`→`forbidLEWith_add_QuadraticForm`,
   `inducedForbidLE_rw_left_add_right`→`forbidLEWith_rw_left_add_right`,
   `inducedForbidLE_of_le`→`forbidLEWith_of_le`, `inducedForbidLE_trans`→`forbidLEWith_trans`,
   `inducedForbidEq_smul`→`forbidEqWith_smul`, `inducedForbidEq_symm`→`forbidEqWith_symm`.
   (Unchanged: `reduce_downward_flagmul`, `expand_one_hfree_at`, `flag_nonneg`,
   `flagsum_ac_sort_rhs_pipeline`, all `simp […]`, matrices, numbers.)

## Key design notes

- **Decidability watch-point (resolved).** `forbiddenCondition H = familyForbiddenCondition
  (forbiddenFlags H)` is an existential over `forbiddenFlags H` (not directly decidable).
  The `_ofMem` expansion lemmas avoid it entirely: they use the **same decidable
  single-clique kill predicate** as the induced version (`0 < flagDensity₁ Fforbid.2
  (unlabel F')`); the per-flag vanishing under `forbiddenCondition H` is discharged from
  `hmem : Fforbid ∈ forbiddenFlags H` via `basisVector_familyForbidEq_zero`.
- **General in the forbidden graph.** The generators take the forbidden `SimpleGraph` + the
  membership term, not a clique size. Cliques pass `completeGraph (Fin r)` +
  `completeSym2Graph_finFlag_mem_forbiddenFlags r`; a future non-clique forbid passes its
  own `SimpleGraph` + its own `… ∈ forbiddenFlags …` lemma.

## REMAINING WORK (ordered)

1. **Build-verify the 7 migrated examples** (`lake build LeanFlagAlgebras.Flagmatic.MantelHfree
   …K3forbidP3 …K3forbidC4 …K3forbidC6 …K4turan …ErdosPentagon`, then `…K5turan` — K5turan is
   the ~11-min one). Fix any per-file slips against the pattern.
2. **Update `Flagmatic/flagmatic_to_lean.py`** — its templates still emit the induced form
   (`=ᵢ[…]`, `inducedForbidLE_*`, the bridge preamble, the old generator-call arity). Bring
   them in line with the migrated `.lean` (which were hand-edited) so future regenerations match.
3. **Delete the induced framework.** ⚠️ Before deleting, `grep -r 'inducedForbid\|≤ᵢ\|=ᵢ'`:
   there are **other consumers** besides the Flagmatic examples —
   - the *curated* `ErdosPentagon/ErdosPentagon.lean` + `ErdosPentagon/Lemmas.lean` prove
     `ErdosPentagon_flagAlgebra : C5.toFlagAlgebra ≤ᵢ[K3.toFinFlag] …` (the hand-written SOS);
   - `Archive/*` files;
   - the non-pruned generators `generate_forbid_mul_theorems` / `generate_forbid_free_mul_theorems`
     in `MulThmGenerator.lean` still emit `=ᵢ`.
   Either migrate/handle these or keep induced for them. Removing the relation defs + notation
   + `inducedForbid*` wrappers + induced expansion lemmas is only safe once nothing references them.
   Keep: `mem_forbiddenFlags_self`, `completeSym2Graph_finFlag_eq`,
   `completeSym2Graph_finFlag_mem_forbiddenFlags`, `forbiddenCondition`, the generic `*With` layer.
4. **Full project build green** (`lake build`, 7999 jobs).
5. (Done) Removed the validation scratch `Flagmatic/OrdinaryForbidPoC.lean`.

## Caveat — pruning is still clique-specialized

The relation layer and the generators are now general in the forbidden graph, but the
forbid-free **flag generation/pruning** still uses the cheap clique check (`hasClique`).
A genuinely non-clique forbid would also need that pruning generalized — a separate effort,
out of scope here.
