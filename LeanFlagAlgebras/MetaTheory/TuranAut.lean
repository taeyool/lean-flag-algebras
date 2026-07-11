import LeanFlagAlgebras.MetaTheory.TuranLimit
import LeanFlagAlgebras.MetaTheory.RootingUniform
import LeanFlagAlgebras.Automation.CompleteGraphFreeP4

/-! # Turán graphs are transitive on rooted patterns (paper §11.5 supporting layer)

Automorphisms of `turanGraph (r·m) r` (`Adj v w ↔ v % r ≠ w % r`) act transitively on
vertices and on ordered pairs of a fixed adjacency pattern.  Consequently **all
`σ`-labellings of a Turán flag are a single flag class** (`labelExtensions` is a
subsingleton) for the one-vertex type `vtype`, the ordered edge type `FlagType_2_1`, and
the ordered non-edge type `FlagType_2_0` — the combinatorial input to the Dirac collapse
of the Turán rooting measures (`TuranDirac`).

Automorphism toolkit: the translation `x ↦ x + c` (residues shift uniformly since
`r ∣ r·m`), the residue-transposition lift (swap two residue classes, fix the rest), and
within-class transpositions.
-/

open SimpleGraph
open scoped Classical

namespace FlagAlgebras.MetaTheory

/-! ## Automorphism toolkit -/

/-- Residues mod `r` in `Fin (r·m)` add up before reduction: since `r ∣ r·m`, the
wrap-around of `Fin`-addition is invisible mod `r`. -/
private lemma val_add_mod (r m : ℕ) [NeZero (r * m)] (c x : Fin (r * m)) :
    ((c + x : Fin (r * m)) : ℕ) % r = ((c : ℕ) + (x : ℕ)) % r := by
  rw [Fin.val_add]
  exact Nat.mod_mod_of_dvd _ ⟨m, rfl⟩

/-- The translation `x ↦ c + x` is an automorphism of the Turán graph: residues shift
uniformly by `c % r`, so residue-inequality is preserved. -/
private def turanTranslate (r m : ℕ) [NeZero (r * m)] (c : Fin (r * m)) :
    turanGraph (r * m) r ≃g turanGraph (r * m) r where
  toEquiv := Equiv.addLeft c
  map_rel_iff' := by
    intro a b
    simp only [Equiv.coe_addLeft, turanGraph_adj, val_add_mod]
    exact not_congr
      ⟨fun h => Nat.ModEq.add_left_cancel' _ h, fun h => Nat.ModEq.add_left _ h⟩

private lemma turanTranslate_apply (r m : ℕ) [NeZero (r * m)] (c x : Fin (r * m)) :
    turanTranslate r m c x = c + x := rfl

/-- A transposition of two same-residue vertices leaves every residue unchanged. -/
private lemma swap_val_mod {r N : ℕ} {a b : Fin N} (hab : (a : ℕ) % r = (b : ℕ) % r)
    (x : Fin N) : ((Equiv.swap a b x : Fin N) : ℕ) % r = (x : ℕ) % r := by
  rcases eq_or_ne x a with rfl | hxa
  · rw [Equiv.swap_apply_left]; exact hab.symm
  · rcases eq_or_ne x b with rfl | hxb
    · rw [Equiv.swap_apply_right]; exact hab
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- The within-class transposition: swapping two vertices of the same residue class is an
automorphism of the Turán graph. -/
private def turanSwapIso (r m : ℕ) {a b : Fin (r * m)}
    (hab : (a : ℕ) % r = (b : ℕ) % r) :
    turanGraph (r * m) r ≃g turanGraph (r * m) r where
  toEquiv := Equiv.swap a b
  map_rel_iff' := by
    intro x y
    simp only [turanGraph_adj]
    rw [swap_val_mod hab x, swap_val_mod hab y]

private lemma turanSwapIso_apply (r m : ℕ) {a b : Fin (r * m)}
    (hab : (a : ℕ) % r = (b : ℕ) % r) (x : Fin (r * m)) :
    turanSwapIso r m hab x = Equiv.swap a b x := rfl

/-- Replacing the residue `i` of `x < r·m` by any other residue `j < r` stays in range. -/
private lemma residue_replace_lt {r m x i j : ℕ} (hxm : x < r * m) (hxi : x % r = i)
    (hj : j < r) : x - i + j < r * m := by
  have hdm : r * (x / r) + i = x := by rw [← hxi]; exact Nat.div_add_mod x r
  have hq : x / r < m := by
    by_contra hq
    push_neg at hq
    have h2 : r * m ≤ r * (x / r) := Nat.mul_le_mul_left r hq
    omega
  have h3 : r * (x / r) + r ≤ r * m := by
    have h4 : r * (x / r + 1) ≤ r * m := Nat.mul_le_mul_left r hq
    rwa [Nat.mul_succ] at h4
  omega

/-- Replacing the residue `i` of `x` by `j < r` indeed produces residue `j`. -/
private lemma residue_replace_mod {r x i j : ℕ} (hxi : x % r = i) (hj : j < r) :
    (x - i + j) % r = j := by
  have hdm : r * (x / r) + i = x := by rw [← hxi]; exact Nat.div_add_mod x r
  have hxeq : x - i + j = r * (x / r) + j := by omega
  rw [hxeq, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-- The residue-transposition lift on vertices: swap the residue classes `i ↔ j`
(`k·r + i ↔ k·r + j` on values), fixing every other class pointwise. -/
private def residueSwapFun (r m : ℕ) (i j : Fin r) (x : Fin (r * m)) : Fin (r * m) :=
  if hxi : (x : ℕ) % r = (i : ℕ) then
    ⟨(x : ℕ) - (i : ℕ) + (j : ℕ), residue_replace_lt x.isLt hxi j.isLt⟩
  else if hxj : (x : ℕ) % r = (j : ℕ) then
    ⟨(x : ℕ) - (j : ℕ) + (i : ℕ), residue_replace_lt x.isLt hxj i.isLt⟩
  else x

private lemma residueSwapFun_val (r m : ℕ) (i j : Fin r) (x : Fin (r * m)) :
    (residueSwapFun r m i j x : ℕ) =
      if (x : ℕ) % r = (i : ℕ) then (x : ℕ) - (i : ℕ) + (j : ℕ)
      else if (x : ℕ) % r = (j : ℕ) then (x : ℕ) - (j : ℕ) + (i : ℕ)
      else (x : ℕ) := by
  unfold residueSwapFun
  split_ifs with h1 h2 <;> rfl

/-- The residue-transposition lift acts on residues as the transposition `i ↔ j`. -/
private lemma residueSwapFun_mod (r m : ℕ) (i j : Fin r) (x : Fin (r * m)) :
    (residueSwapFun r m i j x : ℕ) % r =
      if (x : ℕ) % r = (i : ℕ) then (j : ℕ)
      else if (x : ℕ) % r = (j : ℕ) then (i : ℕ)
      else (x : ℕ) % r := by
  rw [residueSwapFun_val]
  split_ifs with h1 h2
  · exact residue_replace_mod h1 j.isLt
  · exact residue_replace_mod h2 i.isLt
  · rfl

private lemma residueSwapFun_involutive (r m : ℕ) (i j : Fin r) :
    Function.Involutive (residueSwapFun r m i j) := by
  intro x
  apply Fin.ext
  have hx := residueSwapFun_val r m i j x
  have hxm := residueSwapFun_mod r m i j x
  have hy := residueSwapFun_val r m i j (residueSwapFun r m i j x)
  by_cases h1 : (x : ℕ) % r = (i : ℕ)
  · rw [if_pos h1] at hx hxm
    have hile : (i : ℕ) ≤ (x : ℕ) := h1 ▸ Nat.mod_le (x : ℕ) r
    by_cases hij : (i : ℕ) = (j : ℕ)
    · rw [if_pos (hxm.trans hij.symm)] at hy
      omega
    · have hc1 : ¬ ((residueSwapFun r m i j x : ℕ) % r = (i : ℕ)) :=
        fun h => hij (h.symm.trans hxm)
      rw [if_neg hc1, if_pos hxm] at hy
      omega
  · rw [if_neg h1] at hx hxm
    by_cases h2 : (x : ℕ) % r = (j : ℕ)
    · rw [if_pos h2] at hx hxm
      have hjle : (j : ℕ) ≤ (x : ℕ) := h2 ▸ Nat.mod_le (x : ℕ) r
      rw [if_pos hxm] at hy
      omega
    · rw [if_neg h2] at hx hxm
      have hc1 : ¬ ((residueSwapFun r m i j x : ℕ) % r = (i : ℕ)) :=
        fun h => h1 (hxm.symm.trans h)
      have hc2 : ¬ ((residueSwapFun r m i j x : ℕ) % r = (j : ℕ)) :=
        fun h => h2 (hxm.symm.trans h)
      rw [if_neg hc1, if_neg hc2] at hy
      omega

/-- The `ℕ`-level transposition `i ↔ j` is injective (as an if-then-else formula). -/
private lemma natSwap_eq_iff (i j s t : ℕ) :
    ((if s = i then j else if s = j then i else s)
      = (if t = i then j else if t = j then i else t)) ↔ s = t := by
  split_ifs <;> omega

/-- The residue-transposition lift as an automorphism of the Turán graph. -/
private def residueSwapIso (r m : ℕ) (i j : Fin r) :
    turanGraph (r * m) r ≃g turanGraph (r * m) r where
  toEquiv := (residueSwapFun_involutive r m i j).toPerm (residueSwapFun r m i j)
  map_rel_iff' := by
    intro a b
    simp only [Function.Involutive.coe_toPerm, turanGraph_adj, residueSwapFun_mod]
    exact not_congr (natSwap_eq_iff (i : ℕ) (j : ℕ) ((a : ℕ) % r) ((b : ℕ) % r))

private lemma residueSwapIso_apply (r m : ℕ) (i j : Fin r) (x : Fin (r * m)) :
    residueSwapIso r m i j x = residueSwapFun r m i j x := rfl

/-! ## Transitivity of the automorphism group -/

/-- **Vertex transitivity**: the translation `x ↦ x + (v - u)` is an automorphism of the
Turán graph carrying `u` to `v`. -/
theorem turan_vertex_transitive (r m : ℕ) (hm : 0 < m) (u v : Fin (r * m)) :
    ∃ ψ : turanGraph (r * m) r ≃g turanGraph (r * m) r, ψ u = v := by
  -- The `Equiv` is `Equiv.addLeft` on `Fin (r*m)` by `v - u`; adjacency preservation is
  -- `turanTranslate`'s (`Nat.mod_mod_of_dvd` since `r ∣ r*m`, then cancel the shift).
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact absurd u.isLt (by omega)
  · haveI : NeZero (r * m) := ⟨(Nat.mul_pos hr hm).ne'⟩
    refine ⟨turanTranslate r m (v - u), ?_⟩
    rw [turanTranslate_apply]
    exact sub_add_cancel v u

/-- **Ordered-pair transitivity**: any two ordered pairs of distinct vertices with the
same residue-equality pattern are related by an automorphism.  (Same class ↦ same class
via translation + a within-class transposition; different classes ↦ different classes via
translation + a residue-transposition lift + a within-class transposition.) -/
theorem turan_pair_transitive (r m : ℕ) (hm : 0 < m) {u₁ u₂ v₁ v₂ : Fin (r * m)}
    (hu : u₁ ≠ u₂) (hv : v₁ ≠ v₂)
    (hpat : ((u₁ : ℕ) % r = (u₂ : ℕ) % r) ↔ ((v₁ : ℕ) % r = (v₂ : ℕ) % r)) :
    ∃ ψ : turanGraph (r * m) r ≃g turanGraph (r * m) r, ψ u₁ = v₁ ∧ ψ u₂ = v₂ := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact absurd u₁.isLt (by omega)
  -- Step 1: translate `u₁ ↦ v₁`; let `w` be the image of `u₂` (`w ≠ v₁`).
  obtain ⟨ψ₁, hψ₁u₁⟩ := turan_vertex_transitive r m hm u₁ v₁
  set w : Fin (r * m) := ψ₁ u₂ with hw
  have hv₁w : v₁ ≠ w := by
    intro h
    exact hu (ψ₁.injective ((hψ₁u₁.trans h).trans hw))
  -- The pattern of `(v₁, w)` equals that of `(u₁, u₂)` (ψ₁ is an automorphism), hence
  -- that of `(v₁, v₂)` by `hpat`.
  have hclass : ((v₁ : ℕ) % r = (w : ℕ) % r) ↔ ((v₁ : ℕ) % r = (v₂ : ℕ) % r) := by
    have h1 : (turanGraph (r * m) r).Adj v₁ w ↔ (turanGraph (r * m) r).Adj u₁ u₂ := by
      rw [← hψ₁u₁, hw]
      exact ψ₁.map_adj_iff
    simp only [turanGraph_adj] at h1
    exact (not_iff_not.mp h1).trans hpat
  by_cases hwv₂ : (w : ℕ) % r = (v₂ : ℕ) % r
  -- Step 2 (same class): the transposition `w ↔ v₂` is an automorphism fixing `v₁`.
  · refine ⟨ψ₁.trans (turanSwapIso r m hwv₂), ?_, ?_⟩
    · rw [RelIso.trans_apply, hψ₁u₁, turanSwapIso_apply]
      exact Equiv.swap_apply_of_ne_of_ne hv₁w hv
    · rw [RelIso.trans_apply, ← hw, turanSwapIso_apply]
      exact Equiv.swap_apply_left w v₂
  -- Step 3 (different classes): both `w` and `v₂` lie outside `v₁`'s class; lift the
  -- residue transposition `w % r ↔ v₂ % r` (fixes `v₁`, sends `w` into `v₂`'s class),
  -- then finish with the within-class transposition.
  · have hv₁w_mod : (v₁ : ℕ) % r ≠ (w : ℕ) % r :=
      fun h => hwv₂ (h.symm.trans (hclass.mp h))
    have hv₁v₂_mod : (v₁ : ℕ) % r ≠ (v₂ : ℕ) % r :=
      fun h => hwv₂ ((hclass.mpr h).symm.trans h)
    set i : Fin r := ⟨(w : ℕ) % r, Nat.mod_lt _ hr⟩ with hi
    set j : Fin r := ⟨(v₂ : ℕ) % r, Nat.mod_lt _ hr⟩ with hj
    have hival : (i : ℕ) = (w : ℕ) % r := by rw [hi]
    have hjval : (j : ℕ) = (v₂ : ℕ) % r := by rw [hj]
    have hρv₁ : residueSwapIso r m i j v₁ = v₁ := by
      rw [residueSwapIso_apply]
      have hc1 : ¬ ((v₁ : ℕ) % r = (i : ℕ)) := fun h => hv₁w_mod (h.trans hival)
      have hc2 : ¬ ((v₁ : ℕ) % r = (j : ℕ)) := fun h => hv₁v₂_mod (h.trans hjval)
      refine Fin.ext ?_
      rw [residueSwapFun_val, if_neg hc1, if_neg hc2]
    have hρw_mod : ((residueSwapIso r m i j w : Fin (r * m)) : ℕ) % r = (v₂ : ℕ) % r := by
      rw [residueSwapIso_apply, residueSwapFun_mod, if_pos hival.symm]
    have hv₁ρw : v₁ ≠ residueSwapIso r m i j w :=
      fun h => hv₁v₂_mod (by rw [h]; exact hρw_mod)
    refine ⟨(ψ₁.trans (residueSwapIso r m i j)).trans (turanSwapIso r m hρw_mod), ?_, ?_⟩
    · rw [RelIso.trans_apply, RelIso.trans_apply, hψ₁u₁, hρv₁, turanSwapIso_apply]
      exact Equiv.swap_apply_of_ne_of_ne hv₁ρw hv
    · rw [RelIso.trans_apply, RelIso.trans_apply, ← hw, turanSwapIso_apply]
      exact Equiv.swap_apply_left _ v₂

/-! ## `labelExtensions` of a Turán flag is a subsingleton -/

/-- Every element of `labelExtensions` of an unlabelled flag `⟦graphFlag T⟧` has a
representative labelled ON `T` itself: from `unlabel G = ⟦graphFlag T⟧`, extract the
`∅ₜ`-flag iso (whose `graph_iso` is a graph iso `H ≃g T`) and post-compose the type
embedding.  (Template: `sum_isomorphismCount_labelExtensions_fixed`, RootingUniform.) -/
lemma labelExtensions_rep_on_host {n₀ : ℕ} {σ : FlagType (Fin n₀)} {N : ℕ}
    (T : SimpleGraph (Fin N)) (G : FlagWithSize σ N)
    (hG : G ∈ labelExtensions (graphFlag T : Flag ∅ₜ (Fin N)) σ) :
    ∃ θ : σ ↪g T, G = (⟦{ graph := T, type_embed := θ }⟧ : Flag σ (Fin N)) := by
  rcases Quotient.exists_rep G with ⟨H, rfl⟩
  dsimp only [labelExtensions] at hG
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
  -- `hG : unlabel ⟦H⟧ = graphFlag T`; the `∅ₜ`-flag iso is a plain graph iso `H ≃g T`.
  obtain ⟨φ⟩ := unlabel_eq_iff_unlabeledGraph_eqv.mp hG
  have ι : H.graph ≃g T := φ.graph_iso
  refine ⟨H.type_embed.trans ι.toRelEmbedding, flagEqv.sound ?_⟩
  exact ⟨{ graph_iso := ι, type_preserve := rfl }⟩

/-- Two labellings of the same host graph related pointwise by an automorphism give the
same flag class. -/
private lemma turan_labelExtensions_eq {n₀ N : ℕ} {σ : FlagType (Fin n₀)}
    {T : SimpleGraph (Fin N)} {θ₁ θ₂ : σ ↪g T} (ψ : T ≃g T)
    (hψ : ∀ t, ψ (θ₁ t) = θ₂ t) :
    (⟦{ graph := T, type_embed := θ₁ }⟧ : Flag σ (Fin N)) =
      ⟦{ graph := T, type_embed := θ₂ }⟧ :=
  flagEqv.sound ⟨{ graph_iso := ψ, type_preserve := funext hψ }⟩

/-- All `vtype`-labellings of a Turán flag coincide (vertex transitivity). -/
theorem labelExtensions_turan_vtype_subsingleton (r n : ℕ) (_hr : 2 ≤ r) :
    ∀ G₁ ∈ labelExtensions ((turanFlagSeq r n).2) vtype,
    ∀ G₂ ∈ labelExtensions ((turanFlagSeq r n).2) vtype, G₁ = G₂ := by
  intro G₁ hG₁ G₂ hG₂
  obtain ⟨θ₁, h₁⟩ := labelExtensions_rep_on_host (turanGraph (r * (n + 1)) r) G₁ hG₁
  obtain ⟨θ₂, h₂⟩ := labelExtensions_rep_on_host (turanGraph (r * (n + 1)) r) G₂ hG₂
  obtain ⟨ψ, hψ⟩ := turan_vertex_transitive r (n + 1) (Nat.succ_pos n) (θ₁ 0) (θ₂ 0)
  rw [h₁, h₂]
  refine turan_labelExtensions_eq ψ ?_
  intro t
  rw [Subsingleton.elim t 0]
  exact hψ

/-- All ordered-edge labellings (`FlagType_2_1`) of a Turán flag coincide. -/
theorem labelExtensions_turan_edge_subsingleton (r n : ℕ) (_hr : 2 ≤ r) :
    ∀ G₁ ∈ labelExtensions ((turanFlagSeq r n).2) CompleteGraphFreeP4.FlagType_2_1,
    ∀ G₂ ∈ labelExtensions ((turanFlagSeq r n).2) CompleteGraphFreeP4.FlagType_2_1,
      G₁ = G₂ := by
  intro G₁ hG₁ G₂ hG₂
  obtain ⟨θ₁, h₁⟩ := labelExtensions_rep_on_host (turanGraph (r * (n + 1)) r) G₁ hG₁
  obtain ⟨θ₂, h₂⟩ := labelExtensions_rep_on_host (turanGraph (r * (n + 1)) r) G₂ hG₂
  -- The roots of an edge labelling are an ordered pair of ADJACENT vertices, i.e. of
  -- distinct residues: pattern `False ↔ False`.
  have hadj : CompleteGraphFreeP4.FlagType_2_1.Adj 0 1 :=
    (FlagAlgebras.Compute.Sym2FlagType.toFlagType_adj_iff
      CompleteGraphFreeP4.Sym2FlagType_2_1 0 1).mpr (by decide)
  have ha₁ : (turanGraph (r * (n + 1)) r).Adj (θ₁ 0) (θ₁ 1) := θ₁.map_rel_iff.mpr hadj
  have ha₂ : (turanGraph (r * (n + 1)) r).Adj (θ₂ 0) (θ₂ 1) := θ₂.map_rel_iff.mpr hadj
  obtain ⟨ψ, hψ0, hψ1⟩ := turan_pair_transitive r (n + 1) (Nat.succ_pos n) ha₁.ne ha₂.ne
    (iff_of_false (turanGraph_adj.mp ha₁) (turanGraph_adj.mp ha₂))
  rw [h₁, h₂]
  refine turan_labelExtensions_eq ψ ?_
  intro t
  fin_cases t
  · exact hψ0
  · exact hψ1

/-- All ordered-non-edge labellings (`FlagType_2_0`) of a Turán flag coincide. -/
theorem labelExtensions_turan_nonEdge_subsingleton (r n : ℕ) (_hr : 2 ≤ r) :
    ∀ G₁ ∈ labelExtensions ((turanFlagSeq r n).2) CompleteGraphFreeP4.FlagType_2_0,
    ∀ G₂ ∈ labelExtensions ((turanFlagSeq r n).2) CompleteGraphFreeP4.FlagType_2_0,
      G₁ = G₂ := by
  intro G₁ hG₁ G₂ hG₂
  obtain ⟨θ₁, h₁⟩ := labelExtensions_rep_on_host (turanGraph (r * (n + 1)) r) G₁ hG₁
  obtain ⟨θ₂, h₂⟩ := labelExtensions_rep_on_host (turanGraph (r * (n + 1)) r) G₂ hG₂
  -- The roots of a non-edge labelling are an ordered pair of DISTINCT NON-adjacent
  -- vertices, i.e. of equal residues: pattern `True ↔ True`.
  have hnadj : ¬ CompleteGraphFreeP4.FlagType_2_0.Adj 0 1 := fun h =>
    absurd ((FlagAlgebras.Compute.Sym2FlagType.toFlagType_adj_iff
      CompleteGraphFreeP4.Sym2FlagType_2_0 0 1).mp h) (by decide)
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hd₁ : θ₁ 0 ≠ θ₁ 1 := fun h => h01 (θ₁.injective h)
  have hd₂ : θ₂ 0 ≠ θ₂ 1 := fun h => h01 (θ₂.injective h)
  have hm₁ : ((θ₁ 0 : Fin (r * (n + 1))) : ℕ) % r = ((θ₁ 1 : Fin (r * (n + 1))) : ℕ) % r := by
    by_contra hne
    exact hnadj (θ₁.map_rel_iff.mp (turanGraph_adj.mpr hne))
  have hm₂ : ((θ₂ 0 : Fin (r * (n + 1))) : ℕ) % r = ((θ₂ 1 : Fin (r * (n + 1))) : ℕ) % r := by
    by_contra hne
    exact hnadj (θ₂.map_rel_iff.mp (turanGraph_adj.mpr hne))
  obtain ⟨ψ, hψ0, hψ1⟩ := turan_pair_transitive r (n + 1) (Nat.succ_pos n) hd₁ hd₂
    (iff_of_true hm₁ hm₂)
  rw [h₁, h₂]
  refine turan_labelExtensions_eq ψ ?_
  intro t
  fin_cases t
  · exact hψ0
  · exact hψ1

end FlagAlgebras.MetaTheory
