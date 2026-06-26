# Forbid Generalization Refactor Instructions

This note is for an AI agent refactoring `LeanFlagAlgebras/Forbid/Basic.lean`.
The goal is to separate two kinds of generalization that are currently mixed under the
single-forbidden-induced-flag API.

## High-Level Goal

`Forbid.Basic` already starts with a general condition:

```lean
def ForbidCondition : Type := PositiveHom ∅ₜ -> Prop
def forbidEqWith (C : ForbidCondition) ...
def forbidLEWith (C : ForbidCondition) ...
```

but many exported theorems are specialized to:

```lean
inducedForbiddenCondition F_forbid
```

The refactor should introduce condition-parametric theorems where they are genuinely
valid, and keep quotient/pruning expansion theorems specialized to hereditary or
forbidden-family settings where basis terms can actually be killed.

## Important Design Boundary

Do not try to make every theorem work for arbitrary non-hereditary graph classes.

For a non-hereditary limit-level constraint such as `rho = 1/2`, there is usually no
finite basis flag to kill. Such constraints are better represented as a relative
ensemble condition:

```lean
C_Y φ₀ := φ₀ ∈ Y
```

This supports downward soundness, but not quotient-style pruning of expansion sums.

In this refactor:

- Generalize `downward_inducedForbidLE_nonneg` to arbitrary `ForbidCondition`.
- Generalize `basisVector_quot_inducedForbidEq_sum` and
  `basisVector_quot_mul_inducedForbidEq_sum` only through a kill predicate or
  forbidden-family/hereditary-class interface.
- Preserve the existing `inducedForbid...` theorem names as compatibility wrappers.

## Part 1: Condition-Parametric Algebraic API

Many current proofs do not use the particular forbidden flag. They only pass around the
hypothesis `C φ₀`. Add `With` versions for the core algebraic/order lemmas.

Recommended names:

```lean
theorem forbidEqWith_refl
theorem forbidLEWith_refl
theorem forbidEqWith_symm
theorem forbidEqWith_of_eq
theorem forbidLEWith_of_le
theorem forbidLEWith_of_forbidEqWith
theorem forbidEqWith_trans
theorem forbidLEWith_trans
theorem forbidLEWith_antisymm
theorem forbidEqWith_add
theorem forbidLEWith_add
theorem forbidEqWith_smul
theorem forbidLEWith_smul_nonneg
```

Then rewrite the current `inducedForbid...` theorems as thin wrappers, e.g.

```lean
theorem inducedForbidLE_refl (F_forbid : FinFlag ∅ₜ) (f : FlagAlgebra σ) :
    f ≤ᵢ[F_forbid] f :=
  forbidLEWith_refl (C := inducedForbiddenCondition F_forbid) f
```

Keep existing names and notation working. Avoid breaking `API.Basic` and
`TuranDensity`.

## Part 2: Condition-Parametric Downward Soundness

Generalize:

```lean
downward_inducedForbidLE_nonneg_emptyType
downward_inducedForbidLE_nonneg
```

to arbitrary `ForbidCondition`.

Recommended statements:

```lean
theorem downward_forbidLEWith_nonneg_emptyType
    {C : ForbidCondition} {f : FlagAlgebra σ}
    (hf : forbidLEWith C 0 f) :
    forbidLE_emptyTypeWith C 0 ⟦f⟧₀

theorem downward_forbidLEWith_nonneg
    {C : ForbidCondition} {f : FlagAlgebra σ}
    (hf : forbidLEWith C 0 f) :
    forbidLEWith C 0 ⟦f⟧₀
```

Proof plan:

1. Copy the proof of `downward_inducedForbidLE_nonneg_emptyType`.
2. Replace the forbidden flag hypothesis `hF_forbid` with a generic hypothesis `hC : C φ₀`.
3. Invoke `hf φ₀ hσ_pos hC`.
4. For the non-empty-type theorem, use the already existing
   `forbidLE_emptyTypeWith_iff_forbidLEWith`.

Then keep the old theorem as:

```lean
theorem downward_inducedForbidLE_nonneg ... :=
  downward_forbidLEWith_nonneg
    (C := inducedForbiddenCondition F_forbid) hf
```

This is the main theorem that remains meaningful for arbitrary relative constraints
such as equality slices `Y`.

## Part 3: Generic Kill-Predicate Expansion Theorems

The current expansion theorem kills terms using:

```lean
flagDensity₁ F_forbid.2 (unlabel F') > 0
```

For a more general version, introduce a kill predicate and a proof that killed basis
terms are zero under the condition.

Recommended statement:

```lean
theorem basisVector_quot_forbidEqWith_sum_of_kill
    (C : ForbidCondition)
    (Kill : FlagWithSize σ ℓ -> Prop) [DecidablePred Kill]
    (F : FinFlag σ) (ℓ : ℕ) (hℓ : F.1 ≤ ℓ)
    (hkill :
      ∀ F' : FlagWithSize σ ℓ, Kill F' ->
        forbidEqWith C
          (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ)
          0) :
    forbidEqWith C
      (⟦basisVector F⟧ : FlagAlgebra σ)
      (∑ F' : FlagWithSize σ ℓ with ¬ Kill F',
        (flagDensity₁ F.2 F' : ℝ) •
          (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
```

The surviving predicate may also be written as `with Keep F'`, where
`Keep F' := ¬ Kill F'`. Choose whichever is easier for Lean.

Proof plan:

1. Start from `basisVector_quot_eq_sum F ℓ hℓ`.
2. Split the finite sum with `Finset.sum_filter_add_sum_filter_not`.
3. Show the killed part is `forbidEqWith C ... 0` using `hkill`, `forbidEqWith_smul_zero`,
   and `forbidEqWith_sum_filter_eq_zero`.
4. The kept part is reflexive.

Add the multiplication analogue:

```lean
theorem basisVector_quot_mul_forbidEqWith_sum_of_kill
    (C : ForbidCondition)
    (Kill : FlagWithSize σ ℓ -> Prop) [DecidablePred Kill]
    (F₁ F₂ : FinFlag σ) (ℓ : ℕ) (hℓ : F₁.1 + F₂.1 ≤ ℓ + n₀)
    (hkill :
      ∀ F' : FlagWithSize σ ℓ, Kill F' ->
        forbidEqWith C
          (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ)
          0) :
    forbidEqWith C
      ((⟦basisVector F₁⟧ * ⟦basisVector F₂⟧ : FlagAlgebra σ))
      (∑ F' : FlagWithSize σ ℓ with ¬ Kill F',
        (flagDensity₂ F₁.2 F₂.2 F' : ℝ) •
          (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra σ))
```

Proof plan is the same, starting from
`basisVector_quot_mul_eq_flagMulWithSize_quot`.

## Part 4: Forbidden-Family Specialization

After the generic kill-predicate theorem exists, add a specialization for:

```lean
familyForbiddenCondition Fs
```

Use:

```lean
KillFs F' :=
  ∃ D : FinFlag ∅ₜ, D ∈ Fs ∧ flagDensity₁ D.2 (unlabel F') > 0
```

The surviving terms are those satisfying:

```lean
∀ D : FinFlag ∅ₜ, D ∈ Fs -> flagDensity₁ D.2 (unlabel F') = 0
```

The proof requires a family version of `basisVector_inducedForbidEq_zero`.

Recommended theorem:

```lean
theorem basisVector_familyForbidEq_zero
    (Fs : Set (FinFlag ∅ₜ)) (D : FinFlag ∅ₜ) (hD : D ∈ Fs)
    (F : FinFlag σ) (hF : flagDensity₁ D.2 (unlabel F.2) > 0) :
    forbidEqWith (familyForbiddenCondition Fs)
      (⟦basisVector F⟧ : FlagAlgebra σ) 0
```

Proof plan:

Use the existing proof of `basisVector_inducedForbidEq_zero`, replacing the final
condition by:

```lean
hcond D hD : φ₀ ⟦basisVector D⟧ = 0
```

Then prove the `KillFs` version by unpacking the existential.

This specialization is appropriate for hereditary classes encoded as all forbidden
induced flags outside the class, and also for ordinary `H`-free semantics through
`forbiddenFlags H`.

## Part 5: Hereditary-Class Specialization

If this file should stay independent of `MetaTheory.HeredClass`, do not import it into
`Forbid.Basic`. Instead, make the family specialization above strong enough; a later file
can instantiate `Fs` as:

```lean
{D : FinFlag ∅ₜ | underlying graph of D is not in K}
```

If importing `HeredClass` is acceptable in a later refactor, add a theorem whose surviving
condition is directly:

```lean
K.Mem (underlying graph of unlabel F')
```

This is only sound when `K` is hereditary. For hereditary `K`, a flag is admissible iff it
contains no forbidden induced subflag whose underlying graph lies outside `K`.

Do not claim this for arbitrary non-hereditary `K`.

## Part 6: Backward Compatibility Wrappers

Reprove the existing specialized theorems from the new generic ones:

```lean
basisVector_quot_inducedForbidEq_sum
basisVector_quot_mul_inducedForbidEq_sum
downward_inducedForbidLE_nonneg_emptyType
downward_inducedForbidLE_nonneg
```

For the induced single-flag wrappers, use:

```lean
Kill F' := flagDensity₁ F_forbid.2 (unlabel F') > 0
```

and convert `¬ Kill F'` into:

```lean
flagDensity₁ F_forbid.2 (unlabel F') = 0
```

using nonnegativity of flag densities, as the existing proof already does.

## Non-Goals

- Do not make basis-vector pruning for constraints like `φ₀ ρ = 1 / 2`; there is
  generally nothing to kill.
- Do not identify arbitrary non-hereditary graph classes with forbidden induced families.
  That changes the semantics.
- Do not remove existing theorem names or notation.
- Do not refactor `API.Basic` tactics until compatibility wrappers are in place.

## Suggested Verification

After each stage, run:

```powershell
lake env lean LeanFlagAlgebras/Forbid/Basic.lean
lake env lean LeanFlagAlgebras/API/Basic.lean
lake env lean LeanFlagAlgebras/Forbid/TuranDensity.lean
```

If a theorem is used by generated examples, also test:

```powershell
lake env lean LeanFlagAlgebras/Flagmatic/ErdosPentagon.lean
```

---

## Progress (2026-06-26) — DONE, non-breaking, builds green

All six parts carried out in `LeanFlagAlgebras/Forbid/Basic.lean`. The change is **purely
additive**: every new `…With`/generic lemma was introduced, and each existing `inducedForbid…`
theorem was rewritten as a thin compatibility wrapper, so all names + notation are preserved and
no downstream file (`API.Basic`, `TuranDensity`, the generators, the examples) needed any change.

**Verification:** `Forbid.Basic`, `API.Basic`, `Forbid.TuranDensity`, and the generated
`Flagmatic.ErdosPentagon` example all build green (no errors, no `sorry`); full project build green.

### Part 1 — condition-parametric algebraic API ✓
Added the condition-parametric core lemmas and made the induced ones wrappers
(`inducedForbid…_X := forbid…With_X …`):
`forbidEqWith_refl`, `forbidLEWith_refl`, `forbidEqWith_symm`, `forbidEqWith_of_eq`,
`forbidLEWith_of_le`, `forbidLEWith_of_forbidEqWith`, `forbidEqWith_trans`, `forbidLEWith_trans`,
`forbidLEWith_antisymm`, `forbidEqWith_add`, `forbidLEWith_add`, `forbidEqWith_smul`,
`forbidLEWith_smul_nonneg`, plus `forbidEqWith_smul_zero`, `forbidEqWith_sum_eq_zero`,
`forbidEqWith_sum_filter_eq_zero` (needed by Part 3). The proofs are the original ones with the
forbidden-flag hypothesis `hF_forbid` replaced by a generic `hC : C φ₀`. The non-core induced
lemmas (`…_rw_*`, `…_add_left/right`, `…_move_*`, `…_collect_*`) were left as full proofs that call
the (now-wrapper) core lemmas — names preserved, still build.

### Part 2 — condition-parametric downward soundness ✓
`downward_forbidLEWith_nonneg_emptyType` and `downward_forbidLEWith_nonneg` over arbitrary
`C : ForbidCondition` (non-empty via the existing `forbidLE_emptyTypeWith_iff_forbidLEWith`);
`downward_inducedForbidLE_nonneg_emptyType` / `downward_inducedForbidLE_nonneg` are wrappers. This
is the soundness theorem that stays meaningful for arbitrary relative ensemble constraints `C_Y`.

### Part 3 — generic kill-predicate expansion ✓
`basisVector_quot_forbidEqWith_sum_of_kill` and `basisVector_quot_mul_forbidEqWith_sum_of_kill`:
generic over `C` and a `Kill : FlagWithSize σ ℓ → Prop` with `[DecidablePred Kill]` and a hypothesis
`hkill : ∀ F', Kill F' → forbidEqWith C ⟦basisVector ⟨ℓ,F'⟩⟧ 0`; conclusion sums over the surviving
`with ¬ Kill F'`. Proof: `basisVector_quot_eq_sum` → `Finset.sum_filter_add_sum_filter_not` →
killed part `= 0` via `forbidEqWith_sum_filter_eq_zero`/`forbidEqWith_smul_zero`/`hkill`, kept part
reflexive.

### Part 4 — forbidden-family specialization ✓
`basisVector_familyForbidEq_zero` (family version of basis-vector vanishing, proof copied from
`basisVector_inducedForbidEq_zero` with the final density-zero step supplied by `hcond D hD`), and
`basisVector_quot_familyForbidEq_sum` — the family expansion via
`KillFs F' := ∃ D ∈ Fs, flagDensity₁ D.2 (unlabel F') > 0`, surviving terms
`∀ D ∈ Fs, flagDensity₁ D.2 (unlabel F') = 0` (stated as `¬ KillFs`, with an explicit
`[DecidablePred KillFs]` instance argument since `Fs : Set _`).

### Part 5 — hereditary-class specialization ✓ (kept independent)
Did **not** import `MetaTheory.HeredClass` into `Forbid.Basic`. The family specialization (Part 4)
is strong enough; a later file can instantiate `Fs := {D | underlying graph of D ∉ K}` for a
hereditary `K`. (No `K.Mem`-based theorem added here.)

### Part 6 — backward-compatibility wrappers ✓
`basisVector_quot_inducedForbidEq_sum` and `basisVector_quot_mul_inducedForbidEq_sum` reproved from
the generic kill versions with `Kill := fun x => 0 < flagDensity₁ F_forbid.2 (unlabel x)` and
`hkill := basisVector_inducedForbidEq_zero …`. The surviving filter `¬ (0 < d)` is converted to the
original `d = 0` form via `Finset.filter_congr` + nonnegativity of flag densities
(`flagListDensity₁_ge_zero`), so the wrapper's *statement* (and thus all downstream uses) is
unchanged. `downward_inducedForbidLE_nonneg*` likewise wrap Part 2.

### Non-goals respected
No basis-vector pruning was attempted for non-hereditary limit constraints (e.g. `ρ = 1/2`); no
theorem name or notation was removed; `API.Basic` tactics were not touched (the wrappers keep them
compiling as-is).
