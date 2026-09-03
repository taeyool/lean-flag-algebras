import LeanFlagAlgebras.BitMask.RootedCount

/-! # Shared-pass pair counting

At host size 6–7 a per-pair `rmaskCount₂` kernel evaluation re-enumerates
all `4^N` subset pairs (with two extractions + canonicalizations each) for
**every** pattern pair — the dominant cost of the kernel pair-density
route. This module shares that pass: `rootedPairKeys` maps every subset
pair to its *key* — `some (canonical mask₀, canonical mask₁)` when the
structural guard passes, `none` otherwise — so **one** kernel check of
the key multiset against a literal serves every pattern pair of the
host; each pair-density value is then a cheap `Multiset.count` over the
literal (`rmaskCount₂_eq_keyCount`). -/

namespace FlagAlgebras.Compute.BitMask

variable {k N : ℕ} {σ : Sym2FlagType k}

/-- The structural guard of `rmaskCount₂`, verbatim: roots contained in
both subsets, the prescribed cardinalities, disjointness outside the
roots. -/
def rootedPairGuard (G : Sym2LabeledGraph σ N) (m₀ m₁ : ℕ)
    (P : Finset (Fin N) × Finset (Fin N)) : Bool :=
  decide ((Finset.univ.image fun t => G.type_embed t) ⊆ P.1)
    && decide ((Finset.univ.image fun t => G.type_embed t) ⊆ P.2)
    && decide (P.1.card = m₀) && decide (P.2.card = m₁)
    && decide ((P.1 \ (Finset.univ.image fun t => G.type_embed t))
        ∩ (P.2 \ (Finset.univ.image fun t => G.type_embed t)) = ∅)

/-- Per-subset-pair key: the pair of canonical masks of the two rooted
extractions. -/
def rootedPairKey (G : Sym2LabeledGraph σ N) (m₀ m₁ : ℕ)
    (canon₀ canon₁ : ℕ → ℕ) (h : ℕ)
    (P : Finset (Fin N) × Finset (Fin N)) : ℕ × ℕ :=
  (canon₀ (rootedExtractMask m₀ G P.1 h),
   canon₁ (rootedExtractMask m₁ G P.2 h))

/-- The key multiset of the guard-passing subset pairs — computed
**once** per host. Filtering first keeps the multiset (and the literal
the generator compares it against) at the size of the actual placements,
not of all `4^N` subset pairs. -/
def rootedPairKeys (G : Sym2LabeledGraph σ N) (m₀ m₁ : ℕ)
    (canon₀ canon₁ : ℕ → ℕ) (h : ℕ) : Multiset (ℕ × ℕ) :=
  ((Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).val.filter
    (fun P => rootedPairGuard G m₀ m₁ P = true)).map
    (rootedPairKey G m₀ m₁ canon₀ canon₁ h)

/-- `rmaskCount₂` with canonical-comparison accepts is a key count: once
the host's key multiset is identified with a literal `K`, every pattern
pair's count is `K.count (p₀, p₁)` — no re-enumeration. -/
theorem rmaskCount₂_eq_keyCount {G : Sym2LabeledGraph σ N} {m₀ m₁ : ℕ}
    {canon₀ canon₁ : ℕ → ℕ} {h p₀ p₁ : ℕ}
    {K : Multiset (ℕ × ℕ)}
    (hkeys : rootedPairKeys G m₀ m₁ canon₀ canon₁ h = K) :
    rmaskCount₂ G m₀ m₁ (fun x => canon₀ x == p₀) (fun x => canon₁ x == p₁) h
      = Multiset.count (p₀, p₁) K := by
  subst hkeys
  unfold rmaskCount₂ rootedPairKeys
  rw [Finset.card_def, Finset.filter_val, Multiset.count_map,
    Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr ?_
  intro P _
  unfold rootedPairKey rootedPairGuard
  by_cases hg : (decide ((Finset.univ.image fun t => G.type_embed t) ⊆ P.1)
      && decide ((Finset.univ.image fun t => G.type_embed t) ⊆ P.2)
      && decide (P.1.card = m₀) && decide (P.2.card = m₁)
      && decide ((P.1 \ (Finset.univ.image fun t => G.type_embed t))
          ∩ (P.2 \ (Finset.univ.image fun t => G.type_embed t)) = ∅)) = true
  · rw [hg]
    simp only [Bool.true_and, Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq,
      and_true]
    constructor
    · rintro ⟨h₀, h₁⟩
      exact ⟨h₀.symm, h₁.symm⟩
    · rintro ⟨h₀, h₁⟩
      exact ⟨h₀.symm, h₁.symm⟩
  · have hg' : (decide ((Finset.univ.image fun t => G.type_embed t) ⊆ P.1)
        && decide ((Finset.univ.image fun t => G.type_embed t) ⊆ P.2)
        && decide (P.1.card = m₀) && decide (P.2.card = m₁)
        && decide ((P.1 \ (Finset.univ.image fun t => G.type_embed t))
            ∩ (P.2 \ (Finset.univ.image fun t => G.type_embed t)) = ∅)) = false :=
      Bool.eq_false_iff.mpr hg
    rw [hg', Bool.false_and, Bool.false_and]
    simp

end FlagAlgebras.Compute.BitMask
