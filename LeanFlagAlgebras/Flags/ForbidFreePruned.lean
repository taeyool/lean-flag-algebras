import LeanFlagAlgebras.FlagAlgebra.Compute.Generate

/-! # Genuine pruned augmentation (K₃-free, empty-typed graph level)

A *true* pruned augmentation: it builds the triangle-free `n`-vertex graphs by
augmenting only triangle-free `(n-1)`-vertex representatives and keeping only the
triangle-free results, so the forbidden (triangle-containing) graphs are **never
generated**. Contrast with the filter-based forbid-free generator in
`ForbidFreeGenerator.lean`, which computes the full enumeration and filters it.

We use a *combinatorial* triangle predicate `hasTri` (decidable), for which the two
facts the completeness induction needs — isomorphism invariance and monotonicity
under vertex deletion (`restrict`) — are clean to prove. The remaining step needed to
plug this into the forbid bridges, namely `triFree G ↔ flagDensity₁ K3 (unlabel ⟦G⟧) = 0`
(combinatorial vs. analytic forbid-freeness), is **not** proved here; see the note at
the end of the file.
-/

namespace FlagAlgebras.Compute

variable {n : ℕ}

/-- `G` contains a triangle: three distinct, pairwise-adjacent vertices. -/
def hasTri (G : Sym2Graph n) : Prop :=
  ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    s(a, b) ∈ G.edges ∧ s(a, c) ∈ G.edges ∧ s(b, c) ∈ G.edges

instance (G : Sym2Graph n) : Decidable (hasTri G) := by unfold hasTri; infer_instance

/-- Boolean triangle-free test. -/
def triFreeB (G : Sym2Graph n) : Bool := !decide (hasTri G)

theorem triFreeB_eq_true {G : Sym2Graph n} : triFreeB G = true ↔ ¬ hasTri G := by
  simp [triFreeB]

/-- All triangle-free one-vertex augmentations of `G`. -/
def augmentAllTriFree (G : Sym2Graph n) : List (Sym2Graph (n + 1)) :=
  (augmentAll G).filter triFreeB

/-- Pruned augmentation generator: augment only triangle-free representatives and keep
only the triangle-free augmentations. Never builds a triangle-containing graph. -/
def augRepsTriFree : (n : ℕ) → List (Sym2Graph n)
  | 0 => [⟨∅, by simp⟩]
  | n + 1 => ((augRepsTriFree n).flatMap augmentAllTriFree).foldl dedupStep []

/-- `hasTri` is an isomorphism invariant: a triangle transports along the edge-preserving
permutation given by `G ∼sf R`. -/
theorem hasTri_of_eqv {G R : Sym2Graph n} (h : G ∼sf R) (hG : hasTri G) : hasTri R := by
  obtain ⟨φ, hφ⟩ := edge_mem_iff_of_eqv h
  obtain ⟨a, b, c, hab, hac, hbc, eab, eac, ebc⟩ := hG
  refine ⟨φ a, φ b, φ c,
    fun he => hab (φ.injective he), fun he => hac (φ.injective he),
    fun he => hbc (φ.injective he), ?_, ?_, ?_⟩
  · have := (hφ s(a, b)).mp eab; rwa [Sym2.map_pair_eq] at this
  · have := (hφ s(a, c)).mp eac; rwa [Sym2.map_pair_eq] at this
  · have := (hφ s(b, c)).mp ebc; rwa [Sym2.map_pair_eq] at this

/-- **Vertex-deletion monotonicity.** A triangle in the restriction (first `n` vertices)
is a triangle in the whole graph; contrapositively, triangle-freeness is preserved by
`restrict`. This is the key fact that lets the pruned recursion never look at the
forbidden graphs. -/
theorem hasTri_of_restrict {H : Sym2Graph (n + 1)} (h : hasTri (restrict H)) : hasTri H := by
  obtain ⟨a, b, c, hab, hac, hbc, eab, eac, ebc⟩ := h
  refine ⟨Fin.castSucc a, Fin.castSucc b, Fin.castSucc c,
    fun he => hab (Fin.castSucc_injective n he),
    fun he => hac (Fin.castSucc_injective n he),
    fun he => hbc (Fin.castSucc_injective n he), ?_, ?_, ?_⟩
  · have := ((mem_restrict_edges H _).mp eab).2; rwa [Sym2.map_pair_eq] at this
  · have := ((mem_restrict_edges H _).mp eac).2; rwa [Sym2.map_pair_eq] at this
  · have := ((mem_restrict_edges H _).mp ebc).2; rwa [Sym2.map_pair_eq] at this

/-- **Completeness of the pruned generator.** Every triangle-free graph is `∼sf` to a
representative produced by `augRepsTriFree` — even though the generator never enumerated
the triangle-containing graphs. Mirrors `augReps_complete`, using monotonicity to descend
to the restriction and iso-invariance to keep the matched augmentation triangle-free. -/
theorem augRepsTriFree_complete : ∀ (n : ℕ) (G : Sym2Graph n), ¬ hasTri G →
    ∃ R ∈ augRepsTriFree n, G ∼sf R
  | 0 => by
    intro G _
    haveI : IsEmpty (Sym2 (Fin 0)) :=
      ⟨fun e => by induction e using Sym2.ind with | _ a b => exact a.elim0⟩
    refine ⟨⟨∅, by simp⟩, List.mem_cons_self, ?_⟩
    exact sym2GraphEqv_of_equiv (Equiv.refl (Fin 0)) (fun e => isEmptyElim e)
  | n + 1 => by
    intro H hH
    have hRestr : ¬ hasTri (restrict H) := fun htri => hH (hasTri_of_restrict htri)
    obtain ⟨R₀, hR₀mem, hR₀iso⟩ := augRepsTriFree_complete n (restrict H) hRestr
    obtain ⟨S', hS'⟩ := augment_transport hR₀iso (neighborsOfLast H)
    have hHiso : H ∼sf augment R₀ S' := by rw [augment_restrict_eq H]; exact hS'
    have hAug : ¬ hasTri (augment R₀ S') :=
      fun htri => hH (hasTri_of_eqv (Sym2GraphEqv.symm hHiso) htri)
    have hmemFilt : augment R₀ S' ∈ augmentAllTriFree R₀ := by
      rw [augmentAllTriFree]
      exact List.mem_filter.mpr ⟨mem_augmentAll R₀ S', triFreeB_eq_true.mpr hAug⟩
    have hmemFlat : augment R₀ S' ∈ (augRepsTriFree n).flatMap augmentAllTriFree :=
      List.mem_flatMap.mpr ⟨R₀, hR₀mem, hmemFilt⟩
    obtain ⟨R, hRmem, hRiso⟩ :=
      foldl_dedupStep_complete ((augRepsTriFree n).flatMap augmentAllTriFree) []
        (augment R₀ S') hmemFlat
    exact ⟨R, hRmem, Sym2GraphEqv.trans hHiso hRiso⟩

-- Correctness validation (each reduces only the pruned generation, never the full
-- enumeration): the pruned generator produces exactly the known K₃-free class counts
-- (7 of 11 at n=4, 14 of 34 at n=5, 38 of 156 at n=6).
example : (augRepsTriFree 4).length = 7 := by native_decide
example : (augRepsTriFree 5).length = 14 := by native_decide
example : (augRepsTriFree 6).length = 38 := by native_decide

/-! ## Remaining step: connecting to the forbid bridges

`augRepsTriFree` together with `augRepsTriFree_complete` is a genuine pruned generator:
it builds and certifies exactly the triangle-free isomorphism classes without ever
constructing a triangle-containing graph. To replace the filter-based `genFlagsHfree`
(and obtain the measured generation speed-up inside the `flagSetHfree_…_eq` completeness),
one further lemma is needed — the bridge between this *combinatorial* predicate and the
*analytic* one the forbid framework uses:

  `triFree G ↔ flagDensity₁ K3.toFinFlag.2 (unlabel ⟦G⟧) = 0`

i.e. "`G` has no triangle" iff "the K₃-density in `G` is zero". This is the
combinatorial-to-density direction discussed in the design notes; it is not proved here.
With it, `genFlagsHfree_toFinset_eq` could cite `augRepsTriFree_complete` in place of
`genSym2GraphsDedup_complete`, and the line-469 `native_decide` would reduce the pruned
build (~3.2s at n=6) rather than the full enumeration (~5.7s). -/

end FlagAlgebras.Compute
