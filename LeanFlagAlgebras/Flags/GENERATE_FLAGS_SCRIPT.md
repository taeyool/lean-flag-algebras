# Pure-Lean Flag Generation: Replace JSON Pipeline with Lean Algorithm

## Overview

This document is a complete implementation brief. Your job is to replace the Python/JSON-based
flag enumeration pipeline with a self-contained Lean 4 implementation. **Start with empty-typed
(∅ₜ) flags only (Phase 1), verify it fully works, then extend to general typed flags (Phase 2).**

---

## Background: The Problem

The project formalizes flag algebras. Currently:

1. Python scripts (`generate_graphs.py`, `generate_flags.py`) enumerate all non-isomorphic graphs
   and flags, writing them to JSON files (`graphs_n.json`, `flags_n_k_m.json`).
2. Lean's `load_empty_typed_flags`/`load_flags` macros in `LeanFlagAlgebras/Flags/FlagLoader.lean`
   read JSON at elaboration time and generate named constants plus completeness theorems:

```lean
theorem sym2FlagSet_{n}_{k}_{m}_eq_univ : sym2FlagSet_{n}_{k}_{m} = Finset.univ := by
  native_decide   -- ← THIS IS PROHIBITIVELY SLOW for n ≥ 6
```

This `native_decide` forces Lean to enumerate ALL elements of the quotient type `Sym2Flag σ n`
(all iso classes of n-vertex σ-labeled graphs). For n=6 this means 2^15 × 720 ≈ 23 million
raw graphs to process — too slow to be usable.

**The fix**: implement a generation algorithm in Lean and prove its completeness mathematically
(once, for all n), so `= univ` never requires a brute-force computation again.

---

## Existing Infrastructure — Read These Files First, Do Not Modify Them

| File | What it provides |
|------|-----------------|
| `LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean` | Types `Sym2Graph n`, `Sym2EmptyTypedFlag n`, `Sym2LabeledGraph σ n`, `Sym2Flag σ n`; their quotient setoids; `Fintype` instances for all four |
| `LeanFlagAlgebras/FlagAlgebra/Compute/FastIso.lean` | `isEmptyIsoFast_bool`, `isIsoFast_bool` and their soundness/completeness theorems; fast `Decidable`/`Fintype` instances |
| `LeanFlagAlgebras/FlagAlgebra/Compute/Downward.lean` | `downwardNormalizingFactor_sym2LabeledGraph` — already a computable Lean definition of the downward coefficient (no Python needed) |
| `LeanFlagAlgebras/Flags/FlagLoader.lean` | Current slow macros (reference for what constants to generate) |
| `LeanFlagAlgebras/Flags/FlagDef.lean` | Current macro call sites (will be updated in each phase) |

Key facts from these files:
- `Fintype (Sym2Graph n)` exists at Basic.lean:139 — so `Finset.univ : Finset (Sym2Graph n)` works.
- `Fintype (Sym2LabeledGraph σ n)` exists at Basic.lean:443 — same for typed flags.
- `isEmptyIsoFast_bool G₁ G₂ : Bool` and `isIsoFast_bool G₁ G₂ : Bool` are already proven sound
  and complete against `∼sf` (flag equivalence).
- `downwardNormalizingFactor_sym2LabeledGraph G : ℚ` is already defined in Downward.lean:94.

---

## Phase 1: Empty-Typed Flags ← DO THIS FIRST

### Goal

For each `n : ℕ`, produce:
- A computable `genSym2Graphs (n : ℕ) : List (Sym2Graph n)` with one representative per iso class.
- A mathematical proof that this list is complete and nodup.
- A new elab command `generate_empty_typed_flags n` that generates the same named constants as
  the old JSON-based `load_empty_typed_flags`, but without any JSON file, and with `= univ` proved
  by the mathematical theorem instead of `native_decide`.

### Step 1.1 — Create `LeanFlagAlgebras/FlagAlgebra/Compute/Generate.lean`

This file must:
- Import `LeanFlagAlgebras.FlagAlgebra.Compute.FastIso`
- Be imported by `LeanFlagAlgebras/Flags/FlagLoader.lean` (add to the import chain there)

#### 1.1.a — The generation function

```lean
namespace FlagAlgebras.Compute

/-- All raw Sym2Graph n, one per element of Fintype. -/
def allRawSym2Graphs (n : ℕ) : List (Sym2Graph n) :=
  (Finset.univ : Finset (Sym2Graph n)).val.toList

/-- Canonical iso-class representatives: iterate over allRawSym2Graphs n and keep
    the first representative from each equivalence class. -/
def genSym2Graphs (n : ℕ) : List (Sym2Graph n) :=
  allRawSym2Graphs n |>.foldl
    (fun acc G => if acc.any (fun G' => isEmptyIsoFast_bool G' G) then acc else acc ++ [G])
    []

/-- Quotient map of genSym2Graphs: the canonical list as Sym2EmptyTypedFlag elements. -/
def genEmptyTypedFlags (n : ℕ) : List (Sym2EmptyTypedFlag n) :=
  (genSym2Graphs n).map (Quotient.mk (Sym2GraphSetoid n))

/-- The canonical flags as a Finset. -/
def genEmptyTypedFlagSet (n : ℕ) : Finset (Sym2EmptyTypedFlag n) :=
  (genEmptyTypedFlags n).toFinset
```

#### 1.1.b — Completeness theorem

```lean
/-- Every Sym2Graph has a representative in genSym2Graphs n. -/
theorem genSym2Graphs_complete (n : ℕ) :
    ∀ G : Sym2Graph n, ∃ G' ∈ genSym2Graphs n, G ∼sf G'
```

**Proof strategy (by induction on the list processed by foldl):**

You need a helper lemma about the foldl loop invariant:

```lean
private lemma genSym2Graphs_foldl_complete (n : ℕ) :
    ∀ (xs : List (Sym2Graph n)) (acc : List (Sym2Graph n)),
      ∀ G ∈ xs,
        ∃ G' ∈ (xs.foldl
          (fun a G => if a.any (fun G' => isEmptyIsoFast_bool G' G) then a else a ++ [G])
          acc),
          G ∼sf G' := by
  intro xs
  induction xs with
  | nil => intro acc G h; exact absurd h (List.not_mem_nil _)
  | cons x rest ih =>
      intro acc G hG
      simp only [List.foldl_cons]
      cases hG with
      | head =>
          -- G = x (the head)
          by_cases h : acc.any (fun G' => isEmptyIsoFast_bool G' x) = true
          · -- x is already covered by acc
            simp [h]
            -- acc.any = true means ∃ G' ∈ acc, G' ∼sf x
            -- Use isEmptyIsoFast_bool_true_correct to extract witness from acc
            rw [List.any_eq_true] at h
            obtain ⟨G', hG'_mem, hiso⟩ := h
            have heqv := isEmptyIsoFast_bool_true_correct hiso
            -- G' is in acc, which is ⊆ the foldl result (acc grows monotonically)
            -- Need monotonicity lemma: acc ⊆ foldl result
            exact ⟨G', foldl_subset_acc (by exact List.mem_of_mem_append_left hG'_mem) _, heqv.symm⟩
          · -- x is not yet covered: it gets added to acc
            simp [Bool.not_eq_true.mp h]
            apply ih
            -- x is in the new acc = acc ++ [x]
            exact ⟨x, List.mem_append_right _ (List.mem_singleton.mpr rfl), Sym2GraphEqv.refl _⟩
      | tail _ hG_rest =>
          -- G ∈ rest: apply ih
          exact ih _ G hG_rest
```

You will also need a monotonicity lemma showing `acc ⊆ foldl result` (the accumulator only grows).
Write this first:

```lean
private lemma foldl_addIfNew_mono (n : ℕ) (xs : List (Sym2Graph n)) (acc : List (Sym2Graph n)) :
    ∀ G ∈ acc, G ∈ xs.foldl
      (fun a G => if a.any (fun G' => isEmptyIsoFast_bool G' G) then a else a ++ [G]) acc := by
  intro G hG
  induction xs generalizing acc with
  | nil => simpa
  | cons x rest ih =>
      simp only [List.foldl_cons]
      split
      · exact ih acc hG
      · exact ih (acc ++ [x]) (List.mem_append_left _ hG)
```

Then the main theorem follows by applying the helper to `xs = allRawSym2Graphs n`:

```lean
theorem genSym2Graphs_complete (n : ℕ) :
    ∀ G : Sym2Graph n, ∃ G' ∈ genSym2Graphs n, G ∼sf G' := by
  intro G
  have hG_in_all : G ∈ allRawSym2Graphs n := by
    simp [allRawSym2Graphs, Finset.mem_val, Finset.mem_univ]
  exact genSym2Graphs_foldl_complete n (allRawSym2Graphs n) [] G hG_in_all
```

#### 1.1.c — Nodup theorem

```lean
/-- The canonical list has pairwise non-isomorphic elements (nodup as a quotient list). -/
theorem genEmptyTypedFlags_nodup (n : ℕ) : (genEmptyTypedFlags n).Nodup
```

**Proof strategy (by foldl induction with nodup invariant):**

```lean
private lemma genSym2Graphs_foldl_nodup (n : ℕ) :
    ∀ (xs : List (Sym2Graph n)) (acc : List (Sym2Graph n)),
      (acc.map (Quotient.mk (Sym2GraphSetoid n))).Nodup →
        ((xs.foldl
          (fun a G => if a.any (fun G' => isEmptyIsoFast_bool G' G) then a else a ++ [G])
          acc).map (Quotient.mk (Sym2GraphSetoid n))).Nodup := by
  intro xs
  induction xs with
  | nil => intro acc h; simpa
  | cons x rest ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      split
      · -- x already covered: acc unchanged, apply ih
        exact ih acc hacc
      · -- x not covered: added to acc
        rename_i h
        apply ih
        -- Need nodup for (acc ++ [x]).map ...
        simp [List.map_append, List.nodup_append]
        refine ⟨hacc, List.nodup_singleton _, ?_⟩
        -- ⟦x⟧ ∉ acc.map ⟦·⟧
        intro hx_in
        -- If ⟦x⟧ were in acc.map, then acc.any (isEmptyIsoFast_bool · x) = true
        -- contradicting h (the if-condition was false)
        rw [List.any_eq_false] at h
        -- Use isEmptyIsoFast_bool_false_correct and membership
        simp [List.mem_map] at hx_in
        obtain ⟨G', hG'_acc, hiso⟩ := hx_in
        have : isEmptyIsoFast_bool G' x = true := by
          apply isEmptyIsoFast_bool_complete -- you may need to derive this from
          -- isEmptyIsoFast_bool_false_correct by contrapositive
          exact Quotient.exact hiso
        exact absurd this (h G' hG'_acc)
```

Note: you need `isEmptyIsoFast_bool_complete : G ∼sf G' → isEmptyIsoFast_bool G G' = true`.
This should follow from `isEmptyIsoFast_bool_false_correct` by contrapositive:
```lean
lemma isEmptyIsoFast_bool_complete {n} {G G' : Sym2Graph n} (h : G ∼sf G') :
    isEmptyIsoFast_bool G G' = true := by
  by_contra hfalse
  exact (isEmptyIsoFast_bool_false_correct (Bool.eq_false_of_ne_true hfalse)) h
```

Then:
```lean
theorem genEmptyTypedFlags_nodup (n : ℕ) : (genEmptyTypedFlags n).Nodup := by
  simp [genEmptyTypedFlags, genSym2Graphs]
  exact genSym2Graphs_foldl_nodup n (allRawSym2Graphs n) [] (by simp)
```

#### 1.1.d — The `= univ` theorem

```lean
theorem genEmptyTypedFlagSet_eq_univ (n : ℕ) :
    genEmptyTypedFlagSet n = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro F
  simp [genEmptyTypedFlagSet, genEmptyTypedFlags, List.mem_toFinset, List.mem_map]
  rcases Quotient.exists_rep F with ⟨G, rfl⟩
  obtain ⟨G', hG'_mem, hiso⟩ := genSym2Graphs_complete n G
  exact ⟨G', hG'_mem, Quotient.sound hiso⟩
```

### Step 1.2 — New elab command: `generate_empty_typed_flags`

Add a new command to `FlagLoader.lean` (or a new file `FlagGeneratorNew.lean`) that generates
the same constants as `load_empty_typed_flags` but without JSON.

#### How to get the count at elaboration time

The macro needs to know how many graphs there are for vertex count `n` in order to generate
`count` many named constants. Use `unsafe Lean.Meta.evalExpr` to evaluate
`(genSym2Graphs n).length` natively at elaboration time:

```lean
open Lean Meta Elab Command in
unsafe def evalGraphCount (n : ℕ) : CommandElabM ℕ := do
  liftTermElabM do
    let e := mkApp (mkConst ``FlagAlgebras.Compute.genSym2Graphs) (mkNatLit n)
    let lenE := mkApp2 (mkConst ``List.length [Level.zero]) (mkConst ``FlagAlgebras.Compute.Sym2Graph) e
    evalExpr ℕ (mkConst ``Nat) lenE
```

If `unsafe Lean.Meta.evalExpr` is not available or causes issues, use this alternative: define a
`decidable` computation of the count and use `Lean.Elab.Tactic.decide`-style evaluation.
As a last resort, accept the count as a second parameter to the macro:
`generate_empty_typed_flags 5 34` where `34` is the count (pass this explicitly).

#### The generated constants (same names as the JSON loader)

For vertex count `n` and index `i` in `[0, count)`, generate:

```lean
-- The canonical list (defined once, shared)
private def _genSym2GraphList_{n} : List (Sym2Graph {n}) :=
  FlagAlgebras.Compute.genSym2Graphs {n}

-- Individual named graph
def Sym2Graph_{n}_0_0_{i} : Sym2Graph {n} :=
  _genSym2GraphList_{n}[{i}]'(by native_decide)

-- Individual named empty-typed flag (Sym2EmptyTypedFlag)
def Sym2Flag_{n}_0_0_{i} : Sym2EmptyTypedFlag {n} :=
  Quotient.mk (Sym2GraphSetoid {n}) (Sym2Graph_{n}_0_0_{i})

-- Bridge to abstract Flag type
def Flag_{n}_0_0_{i} := (Sym2Flag_{n}_0_0_{i} : Sym2EmptyTypedFlag {n}).toFlag

-- FlagAlgebra element
noncomputable def FlagAlgebra_{n}_0_0_{i} : FlagAlgebras.FlagAlgebra ∅ₜ :=
  ⟦FlagAlgebras.unitVector ⟨{n}, Flag_{n}_0_0_{i}⟩⟧
```

**Important**: The bounds proof `by native_decide` in `_genSym2GraphList_{n}[{i}]'(...)` checks
`{i} < _genSym2GraphList_{n}.length` using native compilation. This compiles `genSym2Graphs {n}`
once and is fast. Subsequent uses of `Sym2Graph_{n}_0_0_{i}` in `native_decide` proofs will
also be fast because native code is cached.

#### The set and completeness constants

```lean
-- The canonical flag set (just the Lean-generated one)
def Sym2FlagSet_{n}_0_0 : Finset (Sym2EmptyTypedFlag {n}) :=
  FlagAlgebras.Compute.genEmptyTypedFlagSet {n}

-- Completeness theorem: NO native_decide needed!
theorem Sym2FlagSet_{n}_0_0_eq_univ : Sym2FlagSet_{n}_0_0 = Finset.univ :=
  FlagAlgebras.Compute.genEmptyTypedFlagSet_eq_univ {n}

-- flagSet (the Flag ∅ₜ version)
def flagSet_{n}_0_0 :=
  Finset.map
    { toFun := Sym2EmptyTypedFlag.toFlag, inj' := Sym2EmptyTypedFlag.toFlag_injective }
    Sym2FlagSet_{n}_0_0

-- flagSet = univ (follows from Sym2FlagSet = univ)
theorem flagSet_{n}_0_0_eq_univ : flagSet_{n}_0_0 = Finset.univ := by
  change Finset.map ... Sym2FlagSet_{n}_0_0 = Finset.univ
  rw [Sym2FlagSet_{n}_0_0_eq_univ]
  exact Finset.map_univ_of_surjective _ (by
    intro F
    exact ⟨F.toSym2EmptyTypedFlag, FlagAlgebras.Flag.toSym2EmptyTypedFlag_toFlag_eq F⟩)
```

#### What to do about `flagSet_{n}_0_0_val_eq`

The old JSON loader generated a theorem:
```lean
theorem flagSet_{n}_0_0_val_eq :
    (flagSet_{n}_0_0).val = [Flag_{n}_0_0_0, Flag_{n}_0_0_1, ..., Flag_{n}_0_0_{m}]
```

In the new approach, generate this theorem with `by native_decide` (it's just checking equality
of two small multisets, which is fast — no quotient enumeration). Alternatively, skip this theorem
if no downstream code uses it. Check `FlagDef.lean` imports and downstream files to decide.

### Step 1.3 — Update `FlagDef.lean`

Replace:
```lean
load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_0.json"
load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_1.json"
...
load_empty_typed_flags "LeanFlagAlgebras/Flags/Graphs/graphs_5.json"
```

With:
```lean
generate_empty_typed_flags 0
generate_empty_typed_flags 1
generate_empty_typed_flags 2
generate_empty_typed_flags 3
generate_empty_typed_flags 4
generate_empty_typed_flags 5
-- Test with 6 too:
-- generate_empty_typed_flags 6
```

Keep the `load_flags` lines unchanged during Phase 1.

### Step 1.4 — Verify Phase 1

Run:
```
lake build LeanFlagAlgebras.Flags.FlagDef
```

Check that:
1. All `Sym2Graph_n_0_0_i`, `Flag_n_0_0_i`, `FlagAlgebra_n_0_0_i` constants are generated.
2. `flagSet_{n}_0_0_eq_univ` is proved WITHOUT `native_decide` on the quotient enumeration.
3. The build time for n=0..5 is comparable to or faster than the old approach.
4. Optionally: add `generate_empty_typed_flags 6` and verify it is fast.

Also verify downstream files still compile:
```
lake build LeanFlagAlgebras.MantelTheorem.FlagDef
lake build LeanFlagAlgebras.ErdosPentagon.FlagDef
```

---

## Phase 2: General Typed Flags ← DO THIS AFTER PHASE 1 WORKS

### Goal

Extend the approach to `Sym2LabeledGraph σ n` and `Sym2Flag σ n`, replacing:
```lean
load_flags "LeanFlagAlgebras/Flags/Flags/flags_n_k_m.json"
```
with:
```lean
generate_flags {k} {m} {n}
-- where k = type vertex count, m = type index within k-vertex graphs, n = total vertices
```

### Step 2.1 — Add to `Generate.lean`

```lean
/-- All raw Sym2LabeledGraph σ n, one per element of Fintype. -/
def allRawSym2LabeledGraphs {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    List (Sym2LabeledGraph σ n) :=
  (Finset.univ : Finset (Sym2LabeledGraph σ n)).val.toList

/-- Canonical iso-class representatives for σ-typed flags on n vertices. -/
def genSym2LabeledGraphs {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    List (Sym2LabeledGraph σ n) :=
  allRawSym2LabeledGraphs σ n |>.foldl
    (fun acc G => if acc.any (fun G' => isIsoFast_bool G' G) then acc else acc ++ [G])
    []

def genFlags {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) : List (Sym2Flag σ n) :=
  (genSym2LabeledGraphs σ n).map (Quotient.mk (sym2LabeledGraphSetoid σ n))

def genFlagSet {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) : Finset (Sym2Flag σ n) :=
  (genFlags σ n).toFinset
```

### Step 2.2 — Theorems for typed flags

Following exactly the same proof structure as Phase 1, prove:

```lean
theorem genSym2LabeledGraphs_complete {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    ∀ G : Sym2LabeledGraph σ n, ∃ G' ∈ genSym2LabeledGraphs σ n, G ∼sf G'

theorem genFlags_nodup {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    (genFlags σ n).Nodup

theorem genFlagSet_eq_univ {k : ℕ} (σ : Sym2FlagType k) (n : ℕ) :
    genFlagSet σ n = Finset.univ
```

The proofs are structurally identical to the empty-typed versions. Use `isIsoFast_bool` instead
of `isEmptyIsoFast_bool`, and `sym2LabeledGraphEqv` instead of `Sym2GraphEqv`.

### Step 2.3 — The `generate_flags` command

The new `generate_flags k m n` command generates for the type `σ = (k-vertex graph with index m)`:

```lean
-- The type (same as before, defined once per (k, m) pair):
def Sym2FlagType_{k}_{m} : Sym2FlagType {k} := ...  -- from genSym2Graphs k
def FlagType_{k}_{m} := Sym2FlagType_{k}_{m}.toFlagType

-- Canonical labeled graph at index i:
private def _genFlagList_{n}_{k}_{m} :=
  FlagAlgebras.Compute.genSym2LabeledGraphs Sym2FlagType_{k}_{m} {n}

def Sym2LabeledGraph_{n}_{k}_{m}_{i} : Sym2LabeledGraph Sym2FlagType_{k}_{m} {n} :=
  _genFlagList_{n}_{k}_{m}[{i}]'(by native_decide)

def Sym2Flag_{n}_{k}_{m}_{i} : Sym2Flag Sym2FlagType_{k}_{m} {n} :=
  Quotient.mk (sym2LabeledGraphSetoid Sym2FlagType_{k}_{m} {n}) Sym2LabeledGraph_{n}_{k}_{m}_{i}

def Flag_{n}_{k}_{m}_{i} := (Sym2Flag_{n}_{k}_{m}_{i}).toFlag

noncomputable def FlagAlgebra_{n}_{k}_{m}_{i} : FlagAlgebras.FlagAlgebra FlagType_{k}_{m} :=
  ⟦FlagAlgebras.unitVector ⟨{n}, Flag_{n}_{k}_{m}_{i}⟩⟧
```

#### Simp lemmas

The `unlabel_{n}_{k}_{m}_{i}` lemma:
```lean
@[simp]
theorem unlabel_{n}_{k}_{m}_{i} :
    FlagAlgebras.unlabel Flag_{n}_{k}_{m}_{i} = Flag_{n}_0_0_{underlyingIdx} := by
  exact Quotient.sound (FlagAlgebras.flagEqv.refl _)
```

where `underlyingIdx` is the index `j` such that `Sym2Graph_{n}_0_0_{j}` is the underlying graph
of `Sym2LabeledGraph_{n}_{k}_{m}_{i}`. You need this index at macro time. Get it by evaluating:
```
(genSym2LabeledGraphs σ n)[i].edges
```
and finding the `j` such that `genSym2Graphs n)[j].edges` matches. Use `unsafe Lean.Meta.evalExpr`
or native evaluation in the macro to extract this at elaboration time.

The `downward_{n}_{k}_{m}_{i}` theorem:

```lean
@[simp]
theorem downward_{n}_{k}_{m}_{i} :
    ⟦FlagAlgebra_{n}_{k}_{m}_{i}⟧₀ = coeffR • FlagAlgebra_{n}_0_0_{underlyingIdx}
```

where `coeffR` is the downward normalizing coefficient as a real number. Since
`downwardNormalizingFactor_sym2LabeledGraph` is already implemented in `Downward.lean:94`, compute
the coefficient in the macro using `unsafe Lean.Meta.evalExpr` on:
```
downwardNormalizingFactor_sym2LabeledGraph (genSym2LabeledGraphs σ n)[i]
```

The proof of `downward_{n}_{k}_{m}_{i}` is:
```lean
theorem downward_{n}_{k}_{m}_{i} : ⟦FlagAlgebra_{n}_{k}_{m}_{i}⟧₀ = coeffR • FlagAlgebra_{n}_0_0_{j} := by
  have hdnf : FlagAlgebras.downwardNormalizingFactor Flag_{n}_{k}_{m}_{i} = {coeffQ} := by
    rw [FlagAlgebras.Compute.downwardNormalizingFactor_eq]
    native_decide   -- still needed per-flag, but only checks coefficient equality
  change FlagAlgebras.downwardFlagVectorQuot ... = ...
  apply Quotient.sound
  simp [FlagAlgebras.downwardFlagVector, FlagAlgebras.downwardFlag, linearExtension, hdnf]
```

Note: the `native_decide` for `downwardNormalizingFactor_eq` is per-flag and is fast (it checks
equality of two rational numbers, not quotient enumeration). Leave this as-is.

#### The set and completeness constants

```lean
def sym2FlagSet_{n}_{k}_{m} : Finset (Sym2Flag Sym2FlagType_{k}_{m} {n}) :=
  FlagAlgebras.Compute.genFlagSet Sym2FlagType_{k}_{m} {n}

theorem sym2FlagSet_{n}_{k}_{m}_eq_univ : sym2FlagSet_{n}_{k}_{m} = Finset.univ :=
  FlagAlgebras.Compute.genFlagSet_eq_univ Sym2FlagType_{k}_{m} {n}
  -- NO native_decide!

def flagSet_{n}_{k}_{m} :=
  Finset.map { toFun := Sym2Flag.toFlag, inj' := Sym2Flag.toFlag_injective }
    sym2FlagSet_{n}_{k}_{m}

theorem flagSet_{n}_{k}_{m}_eq_univ : flagSet_{n}_{k}_{m} = Finset.univ := by
  ...  -- same pattern as empty-typed version above
```

### Step 2.4 — Update `FlagDef.lean`

Replace all `load_flags "..."` lines with the corresponding `generate_flags k m n` calls.
The type index `m` corresponds to the index in `genSym2Graphs k`, so `Sym2FlagType_{k}_{m}`
must use `(genSym2Graphs k)[m]` as its underlying type graph.

### Step 2.5 — Verify Phase 2

```
lake build LeanFlagAlgebras.Flags.FlagDef
lake build LeanFlagAlgebras.Flags.Densities.DensityLoader   -- if it exists
```

---

## Key Design Decisions

### Named constants use indexed access, not hard-coded edges

```lean
-- NEW (named constant via indexed access):
def Sym2Graph_5_0_0_0 := _genSym2GraphList_5[0]'(by native_decide)

-- OLD (named constant with hard-coded edges from JSON):
def Sym2Graph_5_0_0_0 : Sym2Graph 5 where
  edges := mkEdgeFinset 5 [s(0,1), s(0,2), ...]
  edges_valid := by decide
```

The new approach is fine because:
- `native_decide` (which all downstream proofs use anyway) compiles `genSym2Graphs n` to native
  code, which is fast and cached.
- The `decide` (kernel) proofs for `edges_valid` in the old approach are replaced by the fact
  that `Sym2Graph n` elements already satisfy `edges_valid` by construction.
- No correctness risk: the type system ensures `Sym2Graph_5_0_0_0` is a valid `Sym2Graph 5`.

### The key speedup

| Old approach | New approach |
|---|---|
| `native_decide (sym2FlagSet = Finset.univ)` — must enumerate entire quotient type | `genFlagSet_eq_univ` — mathematical proof, zero computation |
| O(2^(n choose 2) × n!) runtime per n | O(1) proof term |
| Prohibitive for n ≥ 6 | Works for any n |

The per-flag `native_decide` for `downwardNormalizingFactor_eq` remains but is fast (comparing
two rationals, not enumerating iso classes).

---

## What NOT to Change

- `LeanFlagAlgebras/FlagAlgebra/Compute/Basic.lean` — do not modify
- `LeanFlagAlgebras/FlagAlgebra/Compute/FastIso.lean` — do not modify
- `LeanFlagAlgebras/FlagAlgebra/Compute/Downward.lean` — do not modify
- All `downward_{n}_{k}_{m}_{i}` proof logic (only the `= univ` slow part is replaced)
- Python scripts and JSON files (keep them; just don't use them from Lean anymore)
- Any downstream theorem that uses the named constants (they keep the same names and types)
- `MantelTheorem/`, `ErdosPentagon/`, `Flagmatic/`, `API/` directories

---

## Proof Helpers You Will Need

These small helper lemmas are needed by the foldl induction proofs:

```lean
-- foldl accumulator is monotone (elements are never removed)
lemma foldl_addIfNew_mono {α} (key : α → α → Bool) :
    ∀ (xs : List α) (acc : List α) (G : α), G ∈ acc →
      G ∈ xs.foldl (fun a x => if a.any (key · x) then a else a ++ [x]) acc

-- isEmptyIsoFast_bool is complete (converse direction)
lemma isEmptyIsoFast_bool_complete {n} {G G' : Sym2Graph n} (h : G ∼sf G') :
    isEmptyIsoFast_bool G G' = true

-- isIsoFast_bool is complete  
lemma isIsoFast_bool_complete {k n} {σ : Sym2FlagType k} {G G' : Sym2LabeledGraph σ n}
    (h : G ∼sf G') : isIsoFast_bool G G' = true
```

The `isEmptyIsoFast_bool_complete` and `isIsoFast_bool_complete` follow by contrapositive from
`isEmptyIsoFast_bool_false_correct` and `isIsoFast_bool_false_correct` respectively
(both already proven in `FastIso.lean`).

---

## Summary Checklist

### Phase 1 (empty-typed, DO FIRST)
- [ ] Create `LeanFlagAlgebras/FlagAlgebra/Compute/Generate.lean` with `genSym2Graphs`,
      `genEmptyTypedFlags`, `genEmptyTypedFlagSet`
- [ ] Prove `genSym2Graphs_complete`
- [ ] Prove `genEmptyTypedFlags_nodup`
- [ ] Prove `genEmptyTypedFlagSet_eq_univ`
- [ ] Add `generate_empty_typed_flags n` elab command (to `FlagLoader.lean` or new file)
- [ ] Update `FlagDef.lean` to use `generate_empty_typed_flags 0..5`
- [ ] Verify build succeeds, `= univ` proved without quotient enumeration
- [ ] Test with n=6 to confirm the speedup

### Phase 2 (typed flags, DO AFTER PHASE 1)
- [ ] Add `genSym2LabeledGraphs`, `genFlags`, `genFlagSet` to `Generate.lean`
- [ ] Prove `genSym2LabeledGraphs_complete`, `genFlags_nodup`, `genFlagSet_eq_univ`
- [ ] Add `generate_flags k m n` elab command
- [ ] Update `FlagDef.lean` to use `generate_flags` for all typed flag loads
- [ ] Verify build succeeds
- [ ] Test with larger n values

---

## Notes on `unsafe Lean.Meta.evalExpr`

The macro needs to evaluate `(genSym2Graphs n).length` at elaboration time to know how many
constants to generate. Use:

```lean
open Lean Meta Elab Command in
unsafe def getCount (n : ℕ) : CommandElabM ℕ :=
  liftTermElabM <| evalExpr ℕ q(ℕ) q(List.length (FlagAlgebras.Compute.genSym2Graphs $n))
```

The `unsafe` keyword is required because `evalExpr` is `unsafe`. Mark the calling elab command
as `unsafe` too. Lean 4 allows `unsafe elab "..." : command => do ...`.

If `evalExpr` does not work as expected (API may vary by Lean version), fall back to:
```lean
-- Pass count explicitly:
elab "generate_empty_typed_flags" n:num count:num : command => do
  -- use count.getNat for the loop bound
```
and document the expected counts (n=0:1, n=1:1, n=2:2, n=3:4, n=4:11, n=5:34, n=6:156).

Similarly for `generate_flags`, use `evalExpr` to get:
1. The count of flags for the given (k, m, n)
2. The underlying graph index for each flag (for `unlabel_{n}_{k}_{m}_{i}`)
3. The downward coefficient for each flag (for `downward_{n}_{k}_{m}_{i}`)
