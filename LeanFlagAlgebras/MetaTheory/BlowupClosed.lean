import LeanFlagAlgebras.MetaTheory.SubstitutionClosed
import LeanFlagAlgebras.MetaTheory.GraphClassConstraint

/-! # Blow-up-closed hereditary classes — the common generalisation of §5–§7 (paper §7)

Sections 5, 6 and 7 prove root-plantability for clone-closed, true-clone-closed and
substitution-closed classes by *the same argument*: the planted estimate only sees the
*between-class* adjacency (governed by the base graph), never the interior of a blown-up vertex.
The exact closure hypothesis the argument needs is the **single-vertex blow-up property**
(`def:blow-up-closed`): one may always blow up a single vertex of an in-class graph to an
arbitrarily large graph, *choosing* the interior, without leaving the class.

* `oneBlowup G v H` — the blow-up of vertex `v` of `G` to the graph `H` (`def:vertex-blowup`):
  delete `v`, add a copy of `H`, join every vertex of `H` to `v`'s `G`-neighbours.
* `BlowupClosed hc` — for every `G ∈ hc`, vertex `v`, and `N`, there is `H` of order `N` with
  `oneBlowup G v H ∈ hc`.
* `BlowupClosed.toUniform` (`lem:blowup-iterate`) — iterating the single-vertex property over the
  vertices of a base graph yields a *uniform* full blow-up in the class; this is exactly the
  hypothesis `subst_root_plantable` consumes.
* `blowupClosed_root_plantable` (`thm:blowup-root-plantable`) — the unified theorem: every
  blow-up-closed hereditary class is root-plantable.

Clone-closure, true-clone-closure and substitution-closure are each special cases
(`GraphClass.toBlowupClosed` here; the §6/§7 versions in `TrueClone`/`Substitution`), so the three
root-plantability theorems all become corollaries of `blowupClosed_root_plantable`.
-/

namespace FlagAlgebras.MetaTheory

open SimpleGraph

attribute [local instance] Classical.propDecidable

/-! ## The single-vertex blow-up -/

variable {V : Type*}

/-- **Vertex blow-up** (`def:vertex-blowup`): `oneBlowup G v H` deletes `v` from `G`, adds a disjoint
copy of `H` (vertex set `Fin N`), joins every vertex of `H` to every `G`-neighbour of `v`, and keeps
the internal edges of `H`.  Taking `H` edgeless gives a one-vertex independent blow-up; taking `H`
complete gives a one-vertex complete blow-up. -/
def oneBlowup (G : SimpleGraph V) (v : V) {N : ℕ} (H : SimpleGraph (Fin N)) :
    SimpleGraph ({w : V // w ≠ v} ⊕ Fin N) where
  Adj a b :=
    match a, b with
    | Sum.inl w, Sum.inl w' => G.Adj w.1 w'.1
    | Sum.inl w, Sum.inr _ => G.Adj w.1 v
    | Sum.inr _, Sum.inl w' => G.Adj v w'.1
    | Sum.inr i, Sum.inr j => H.Adj i j
  symm := by
    rintro (a | a) (b | b) hab
    · exact G.symm hab
    · exact G.symm hab
    · exact G.symm hab
    · exact H.symm hab
  loopless := by
    rintro (a | a) hab
    · exact G.loopless _ hab
    · exact H.loopless _ hab

/-! ## Membership transport along a graph isomorphism -/

/-- **Membership is isomorphism-invariant.**  Two isomorphic graphs are simultaneously in or out of
the class (`comap` both ways along `e`).  The workhorse for transferring every blow-up identity into
the class. -/
theorem HeredClass.Mem_congr (hc : HeredClass) {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {GA : SimpleGraph A} {GB : SimpleGraph B} (e : GA ≃g GB) :
    hc.Mem GA ↔ hc.Mem GB :=
  ⟨fun h => hc.comap e.symm.toEmbedding h, fun h => hc.comap e.toEmbedding h⟩

/-! ## The single-vertex blow-up as a one-class sub-blow-up -/

variable [DecidableEq V]

/-- The clone-class sizes of the one-vertex blow-up: the blown-up vertex `v` gets `N` clones, every
other vertex keeps a single clone. -/
def oneSize (v : V) (N : ℕ) : V → ℕ := fun w => if w = v then N else 1

@[simp] lemma oneSize_self (v : V) (N : ℕ) : oneSize v N v = N := if_pos rfl

@[simp] lemma oneSize_of_ne {v w : V} (N : ℕ) (h : w ≠ v) : oneSize v N w = 1 := if_neg h

/-- In a singleton `Fin` (size propositionally `1`), any two elements coincide. -/
lemma fin_size_one_eq {k : ℕ} (hk : k = 1) (i j : Fin k) : i = j := by
  subst hk
  exact Subsingleton.elim i j

/-- The within-class family of the one-vertex blow-up: the interior graph `H` at the blown-up vertex
`v` (transported along the size equality `oneSize v N v = N`), and the edgeless one-vertex graph
everywhere else. -/
def oneFamily (v : V) {N : ℕ} (H : SimpleGraph (Fin N)) :
    ∀ w, SimpleGraph (Fin (oneSize v N w)) :=
  fun w =>
    if h : w = v then
      (SimpleGraph.comap (Fin.cast (by rw [h, oneSize_self])) H)
    else (⊥ : SimpleGraph (Fin (oneSize v N w)))

/-- The vertex bijection underlying `oneBlowup_iso`: `inr i` lands in the size-`N` clone class of
`v`, and `inl ⟨w, hw⟩` lands as the unique clone of `w ≠ v`. -/
def oneBlowupEquiv (v : V) (N : ℕ) :
    ({w : V // w ≠ v} ⊕ Fin N) ≃ Σ w, Fin (oneSize v N w) where
  toFun a :=
    match a with
    | Sum.inl w => ⟨w.1, ⟨0, by rw [oneSize_of_ne N w.2]; exact Nat.one_pos⟩⟩
    | Sum.inr i => ⟨v, Fin.cast (oneSize_self v N).symm i⟩
  invFun p :=
    if h : p.1 = v then Sum.inr (Fin.cast (by rw [h, oneSize_self]) p.2)
    else Sum.inl ⟨p.1, h⟩
  left_inv a := by
    cases a with
    | inl w =>
      simp only [dif_neg w.2]
    | inr i =>
      simp only
      refine congrArg Sum.inr (Fin.ext ?_)
      rfl
  right_inv p := by
    obtain ⟨w, x⟩ := p
    by_cases h : w = v
    · subst h
      simp only
      refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
      rfl
    · simp only [dif_neg h]
      exact Sigma.ext rfl (heq_of_eq (fin_size_one_eq (oneSize_of_ne N h) _ _))

/-- **One-vertex blow-up = one-class sub-blow-up** (`def:vertex-blowup` reconciled with
`def:graph-substitution`).  The single-vertex blow-up of `v` of `G` to `H` is, up to relabelling
vertices, the generalised blow-up of `G` whose clone class at `v` is the interior `H` and whose
other clone classes are singletons.  This reduces every single-vertex statement to a `subBlowup`
statement, where class closure operates. -/
noncomputable def oneBlowup_iso (G : SimpleGraph V) (v : V) {N : ℕ} (H : SimpleGraph (Fin N)) :
    oneBlowup G v H ≃g subBlowup G (oneFamily v H) where
  toEquiv := oneBlowupEquiv v N
  map_rel_iff' := by
    intro a b
    -- Split on the four `oneBlowup` cases; the RHS `(oneBlowup G v H).Adj` reduces definitionally.
    cases a with
    | inl w =>
      cases b with
      | inl w' =>
        -- two distinct base vertices `w, w'`; same-class only if `w = w'`.
        change (subBlowup G (oneFamily v H)).Adj ⟨w.1, _⟩ ⟨w'.1, _⟩ ↔ G.Adj w.1 w'.1
        by_cases hww : w'.1 = w.1
        · -- same base ⟹ `inl` clones coincide ⟹ both sides `False`.
          have hwweq : w = w' := Subtype.ext hww.symm
          subst hwweq
          simp only [SimpleGraph.irrefl]
        · rw [subBlowup_adj_of_fst_ne G (oneFamily v H) hww]
      | inr j =>
        -- `inl w` vs `inr j`: distinct base vertices `w.1 ≠ v`.
        change (subBlowup G (oneFamily v H)).Adj ⟨w.1, _⟩ ⟨v, _⟩ ↔ G.Adj w.1 v
        rw [subBlowup_adj_of_fst_ne G (oneFamily v H) (by exact fun h => w.2 h.symm)]
    | inr i =>
      cases b with
      | inl w' =>
        change (subBlowup G (oneFamily v H)).Adj ⟨v, _⟩ ⟨w'.1, _⟩ ↔ G.Adj v w'.1
        rw [subBlowup_adj_of_fst_ne G (oneFamily v H) (by exact w'.2)]
      | inr j =>
        -- both in the size-`N` clone class of `v`; within-class graph is `H`.
        change (G.Adj v v ∨ ∃ h : v = v, (oneFamily v H v).Adj _ (h ▸ _)) ↔ H.Adj i j
        constructor
        · rintro (hG | ⟨_, hint⟩)
          · exact absurd hG (G.loopless v)
          · simp only [oneFamily] at hint
            simpa [Fin.cast] using hint
        · intro hH
          refine Or.inr ⟨rfl, ?_⟩
          simp only [oneFamily]
          simpa [Fin.cast] using hH

/-! ## Reductions of one-class sub-blow-ups to standard blow-ups -/

omit [DecidableEq V] in
/-- A sub-blow-up all of whose clone classes are edgeless is the independent blow-up. -/
lemma subBlowup_eq_independentBlowup (G : SimpleGraph V) {m : V → ℕ}
    (W : ∀ w, SimpleGraph (Fin (m w))) (hW : ∀ w, W w = ⊥) :
    subBlowup G W = independentBlowup G m := by
  ext p q
  rw [independentBlowup_adj]
  show (G.Adj p.1 q.1 ∨ ∃ h : q.1 = p.1, (W p.1).Adj p.2 (h ▸ q.2)) ↔ G.Adj p.1 q.1
  constructor
  · rintro (hG | ⟨h, hint⟩)
    · exact hG
    · rw [hW p.1] at hint; exact absurd hint (by simp)
  · exact Or.inl

/-- The `⊥`-interior one-vertex family is edgeless at every clone class. -/
lemma oneFamily_bot_eq_bot (v : V) (N : ℕ) (w : V) :
    oneFamily v (⊥ : SimpleGraph (Fin N)) w = ⊥ := by
  unfold oneFamily
  split
  · ext a b; simp
  · rfl

/-- The one-vertex blow-up to an **edgeless** interior is the independent blow-up with one enlarged
clone class.  (Used by `GraphClass.toBlowupClosed`.) -/
lemma subBlowup_oneFamily_bot (G : SimpleGraph V) (v : V) (N : ℕ) :
    subBlowup G (oneFamily v (⊥ : SimpleGraph (Fin N))) = independentBlowup G (oneSize v N) :=
  subBlowup_eq_independentBlowup G _ (oneFamily_bot_eq_bot v N)

/-- The `⊤`-interior one-vertex family equals the all-cliques family `fun _ => ⊤`.  At `v` both are
the complete graph (`comap` of an injection of `⊤` is `⊤`); at any other vertex the clone class has
size `1`, on which `⊥` and `⊤` coincide (a single vertex has no edges either way). -/
lemma oneFamily_top_eq_top (v : V) (N : ℕ) (w : V) :
    oneFamily v (⊤ : SimpleGraph (Fin N)) w = (⊤ : SimpleGraph (Fin (oneSize v N w))) := by
  unfold oneFamily
  split
  · ext a b
    simp only [SimpleGraph.comap_adj, SimpleGraph.top_adj]
    exact (Fin.cast_injective _).ne_iff
  · ext a b
    rename_i hwv
    simp only [SimpleGraph.bot_adj, SimpleGraph.top_adj,
      fin_size_one_eq (oneSize_of_ne N hwv) a b, ne_eq, not_true_eq_false]

/-- The one-vertex blow-up to a **complete** interior is the complete blow-up with one enlarged clone
class.  (Used by `TrueCloneClosed.toBlowupClosed`.) -/
lemma subBlowup_oneFamily_top (G : SimpleGraph V) (v : V) (N : ℕ) :
    subBlowup G (oneFamily v (⊤ : SimpleGraph (Fin N))) = completeBlowup G (oneSize v N) := by
  show subBlowup G (oneFamily v (⊤ : SimpleGraph (Fin N)))
      = subBlowup G (fun _ : V => (⊤ : SimpleGraph (Fin (oneSize v N _))))
  congr 1
  funext w
  exact oneFamily_top_eq_top v N w

/-! ## Fibre membership for the substitution case -/

/-- Membership transfers along the `comap` of an equivalence: `comap e G` is isomorphic to `G`. -/
lemma HeredClass.mem_comap_equiv (hc : HeredClass) {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (G : SimpleGraph B) (hG : hc.Mem G) :
    hc.Mem (SimpleGraph.comap e G) :=
  (hc.Mem_congr (A := A) (B := B)
    (GA := SimpleGraph.comap e G) (GB := G)
    { toEquiv := e, map_rel_iff' := by intro a b; simp [SimpleGraph.comap_adj] }).mpr hG

/-- Every clone-class graph of the `H`-interior one-vertex family lies in the class, **provided** the
interior `H` does and every singleton-vertex graph does (the latter holds whenever the class is
nonempty/infinite).  The `v`-fibre is `≃g H`; the size-`1` fibres are the singleton graph. -/
lemma oneFamily_mem {hc : HeredClass} (v : V) {N : ℕ} (H : SimpleGraph (Fin N)) (hH : hc.Mem H)
    (h1 : hc.Mem (⊥ : SimpleGraph (Fin 1))) (w : V) :
    hc.Mem (oneFamily v H w) := by
  unfold oneFamily
  split
  · rename_i hwv
    -- the `v`-fibre: `comap (Fin.cast _) H`, isomorphic to `H`
    subst hwv
    exact hc.mem_comap_equiv (finCongr (oneSize_self w N)) H hH
  · rename_i hwv
    -- a singleton fibre: `⊥ : SimpleGraph (Fin (oneSize v N w))` with `oneSize v N w = 1`
    have hsz : oneSize v N w = 1 := oneSize_of_ne N hwv
    -- transport the singleton membership across the size equality
    have e : (⊥ : SimpleGraph (Fin (oneSize v N w))) ≃g (⊥ : SimpleGraph (Fin 1)) :=
      { toEquiv := finCongr hsz
        map_rel_iff' := by intro a b; simp }
    exact (hc.Mem_congr e).mpr h1

/-! ## The all-singleton sub-blow-up is the base graph -/

/-- A sub-blow-up all of whose clone classes are singletons is (isomorphic to) the base graph. -/
noncomputable def subBlowup_singleton_iso {n : ℕ} (Γ : SimpleGraph (Fin n)) {a : Fin n → ℕ}
    (ha : ∀ w, a w = 1) (W : ∀ w, SimpleGraph (Fin (a w))) :
    subBlowup Γ W ≃g Γ where
  toEquiv :=
    { toFun := fun p => p.1
      invFun := fun w => ⟨w, ⟨0, by rw [ha w]; exact Nat.one_pos⟩⟩
      left_inv := by
        rintro ⟨w, i⟩
        exact Sigma.ext rfl (heq_of_eq (fin_size_one_eq (ha w) _ _))
      right_inv := fun w => rfl }
  map_rel_iff' := by
    rintro ⟨w, i⟩ ⟨w', i'⟩
    show Γ.Adj w w' ↔ (subBlowup Γ W).Adj ⟨w, i⟩ ⟨w', i'⟩
    by_cases hww : w' = w
    · -- same base vertex: singleton clone class forces `i = i'`, both sides irreflexive
      subst hww
      have hi : i = i' := fin_size_one_eq (ha w') i i'
      subst hi
      simp only [SimpleGraph.irrefl]
    · rw [subBlowup_adj_of_fst_ne Γ W hww]

/-! ## The induction step: enlarging one singleton clone class -/

/-- The target within-class family obtained by enlarging the (singleton) clone class of `v` of
`subBlowup Γ W'` to the interior `H`.  At `v` the fibre becomes `H` (size `N`), at every other vertex
it is the old fibre `W' w` (transported across `update a v N w = a w`). -/
noncomputable def stepFamily {n : ℕ} (v : Fin n) {a : Fin n → ℕ} (W' : ∀ w, SimpleGraph (Fin (a w)))
    {N : ℕ} (H : SimpleGraph (Fin N)) :
    ∀ w, SimpleGraph (Fin (Function.update a v N w)) :=
  fun w =>
    if h : w = v then
      SimpleGraph.comap (Fin.cast (show Function.update a v N w = N by rw [h, Function.update_self])) H
    else
      SimpleGraph.comap
        (Fin.cast (show Function.update a v N w = a w from Function.update_of_ne h N a)) (W' w)

/-- The only vertex with base `v` of an `a`-blow-up whose `v`-class is a singleton is `⟨v, 0⟩`. -/
lemma sigma_fst_eq_singleton {n : ℕ} (v : Fin n) {a : Fin n → ℕ} (hav : a v = 1)
    (q : Σ w, Fin (a w)) (hq : q.1 = v) :
    q = ⟨v, ⟨0, by rw [hav]; exact Nat.one_pos⟩⟩ := by
  obtain ⟨w, j⟩ := q
  simp only at hq
  subst hq
  exact Sigma.ext rfl (heq_of_eq (fin_size_one_eq hav _ _))

/-- The vertex bijection underlying `subBlowupStepIso`.  `inr i` lands in the (now size-`N`) clone
class of `v`; `inl q` keeps a non-`v` clone (since the `v`-class was a singleton, every `q ≠ ⟨v,0⟩`
has base `≠ v`). -/
def stepEquiv {n : ℕ} (v : Fin n) {a : Fin n → ℕ} (hav : a v = 1) {N : ℕ} :
    ({q : Σ w, Fin (a w) // q ≠ ⟨v, ⟨0, by rw [hav]; exact Nat.one_pos⟩⟩} ⊕ Fin N)
      ≃ Σ w, Fin (Function.update a v N w) where
  toFun x :=
    match x with
    | Sum.inl q =>
      ⟨q.1.1, Fin.cast (show a q.1.1 = Function.update a v N q.1.1 from
        (Function.update_of_ne (fun hqv => q.2 (sigma_fst_eq_singleton v hav q.1 hqv)) N a).symm)
        q.1.2⟩
    | Sum.inr i => ⟨v, Fin.cast (show N = Function.update a v N v from
        (Function.update_self v N a).symm) i⟩
  invFun p :=
    if h : p.1 = v then
      Sum.inr (Fin.cast (show Function.update a v N p.1 = N by rw [h, Function.update_self]) p.2)
    else
      Sum.inl ⟨⟨p.1, Fin.cast (show Function.update a v N p.1 = a p.1 from
          Function.update_of_ne h N a) p.2⟩,
        fun he => h (congrArg Sigma.fst he)⟩
  left_inv x := by
    cases x with
    | inl q =>
      have hqv : q.1.1 ≠ v := fun hqv => q.2 (sigma_fst_eq_singleton v hav q.1 hqv)
      simp only [dif_neg hqv]
      refine congrArg Sum.inl (Subtype.ext (Sigma.ext rfl (heq_of_eq (Fin.ext ?_))))
      rfl
    | inr i =>
      simp only
      exact congrArg Sum.inr (Fin.ext rfl)
  right_inv p := by
    obtain ⟨w, x⟩ := p
    by_cases h : w = v
    · subst h
      simp only
      exact Sigma.ext rfl (heq_of_eq (Fin.ext rfl))
    · simp only [dif_neg h]
      exact Sigma.ext rfl (heq_of_eq (Fin.ext rfl))

/-- **Induction step iso** for `toUniform`.  When the clone class of `v` of `subBlowup Γ W'` is a
singleton (`a v = 1`), blowing up its unique vertex `⟨v, 0⟩` to the interior `H` yields exactly the
sub-blow-up of `Γ` whose `v`-fibre is `H` and whose other fibres are unchanged.  This is the
single-step of the iteration `lem:blowup-iterate`. -/
noncomputable def subBlowupStepIso {n : ℕ} (Γ : SimpleGraph (Fin n)) (v : Fin n) {a : Fin n → ℕ}
    (hav : a v = 1) (W' : ∀ w, SimpleGraph (Fin (a w))) {N : ℕ} (H : SimpleGraph (Fin N)) :
    oneBlowup (subBlowup Γ W') ⟨v, ⟨0, by rw [hav]; exact Nat.one_pos⟩⟩ H
      ≃g subBlowup Γ (stepFamily v W' H) where
  toEquiv := stepEquiv v hav
  map_rel_iff' := by
    intro a' b'
    cases a' with
    | inl q₁ =>
      have h1 : q₁.1.1 ≠ v := fun hqv => q₁.2 (sigma_fst_eq_singleton v hav q₁.1 hqv)
      cases b' with
      | inl q₂ =>
        have h2 : q₂.1.1 ≠ v := fun hqv => q₂.2 (sigma_fst_eq_singleton v hav q₂.1 hqv)
        change (subBlowup Γ (stepFamily v W' H)).Adj ⟨q₁.1.1, _⟩ ⟨q₂.1.1, _⟩
            ↔ (subBlowup Γ W').Adj q₁.1 q₂.1
        by_cases hww : q₂.1.1 = q₁.1.1
        · -- same base vertex `w` (≠ v)
          obtain ⟨⟨w, j₁⟩, hq₁⟩ := q₁
          obtain ⟨⟨w₂, j₂⟩, hq₂⟩ := q₂
          simp only at hww h1 h2
          subst w₂
          change (Γ.Adj w w ∨ ∃ hh : w = w, (stepFamily v W' H w).Adj _ (hh ▸ _))
              ↔ (Γ.Adj w w ∨ ∃ hh : w = w, (W' w).Adj _ (hh ▸ _))
          have hstep : stepFamily v W' H w
              = SimpleGraph.comap (Fin.cast (by rw [Function.update_of_ne h1])) (W' w) := by
            simp only [stepFamily, dif_neg h1]
          rw [hstep]
          refine or_congr Iff.rfl ?_
          constructor
          · rintro ⟨hh, hadj⟩
            refine ⟨hh, ?_⟩
            simp only [SimpleGraph.comap_adj] at hadj
            simpa [Fin.cast] using hadj
          · rintro ⟨hh, hadj⟩
            refine ⟨hh, ?_⟩
            simp only [SimpleGraph.comap_adj]
            simpa [Fin.cast] using hadj
        · rw [subBlowup_adj_of_fst_ne Γ (stepFamily v W' H) hww,
            subBlowup_adj_of_fst_ne Γ W' hww]
      | inr i' =>
        change (subBlowup Γ (stepFamily v W' H)).Adj ⟨q₁.1.1, _⟩ ⟨v, _⟩
            ↔ (subBlowup Γ W').Adj q₁.1 ⟨v, _⟩
        rw [subBlowup_adj_of_fst_ne Γ (stepFamily v W' H) (Ne.symm h1),
          subBlowup_adj_of_fst_ne Γ W' (Ne.symm h1)]
    | inr i =>
      cases b' with
      | inl q₂ =>
        have h2 : q₂.1.1 ≠ v := fun hqv => q₂.2 (sigma_fst_eq_singleton v hav q₂.1 hqv)
        change (subBlowup Γ (stepFamily v W' H)).Adj ⟨v, _⟩ ⟨q₂.1.1, _⟩
            ↔ (subBlowup Γ W').Adj ⟨v, _⟩ q₂.1
        rw [subBlowup_adj_of_fst_ne Γ (stepFamily v W' H) h2,
          subBlowup_adj_of_fst_ne Γ W' h2]
      | inr i' =>
        -- both `⟨v,·⟩`; within-class `stepFamily v W' H v = H`
        change (Γ.Adj v v ∨ ∃ h : v = v, (stepFamily v W' H v).Adj _ (h ▸ _)) ↔ H.Adj i i'
        constructor
        · rintro (hG | ⟨_, hint⟩)
          · exact absurd hG (Γ.loopless v)
          · simp only [stepFamily] at hint
            simpa [Fin.cast] using hint
        · intro hH
          refine Or.inr ⟨rfl, ?_⟩
          simp only [stepFamily]
          simpa [Fin.cast] using hH

/-! ## Recasting clone sizes along a pointwise equality -/

/-- **Recasting clone sizes.**  If two size families agree pointwise (`s w = t w`), the sub-blow-up
of `Γ` with within-class graphs `V` (over the `t`-sizes) is isomorphic to the sub-blow-up whose
within-class graphs are `V` transported to the `s`-sizes.  This packages a propositional size-family
equality into a graph isomorphism, avoiding dependent `▸` transport. -/
noncomputable def subBlowup_recast_iso {n : ℕ} (Γ : SimpleGraph (Fin n)) {s t : Fin n → ℕ}
    (h : ∀ w, s w = t w) (V : ∀ w, SimpleGraph (Fin (t w))) :
    subBlowup Γ (fun w => SimpleGraph.comap (Fin.cast (h w)) (V w)) ≃g subBlowup Γ V where
  toEquiv :=
    { toFun := fun p => ⟨p.1, Fin.cast (h p.1) p.2⟩
      invFun := fun p => ⟨p.1, Fin.cast (h p.1).symm p.2⟩
      left_inv := by rintro ⟨w, i⟩; exact Sigma.ext rfl (heq_of_eq (Fin.ext rfl))
      right_inv := by rintro ⟨w, i⟩; exact Sigma.ext rfl (heq_of_eq (Fin.ext rfl)) }
  map_rel_iff' := by
    rintro ⟨w, i⟩ ⟨w', i'⟩
    by_cases hww : w' = w
    · subst w'
      change (subBlowup Γ V).Adj ⟨w, Fin.cast (h w) i⟩ ⟨w, Fin.cast (h w) i'⟩
          ↔ (subBlowup Γ (fun w => SimpleGraph.comap (Fin.cast (h w)) (V w))).Adj ⟨w, i⟩ ⟨w, i'⟩
      change (Γ.Adj w w ∨ ∃ hh : w = w, (V w).Adj _ (hh ▸ _))
          ↔ (Γ.Adj w w ∨ ∃ hh : w = w, (SimpleGraph.comap (Fin.cast (h w)) (V w)).Adj _ (hh ▸ _))
      refine or_congr Iff.rfl ?_
      constructor
      · rintro ⟨hh, hadj⟩
        refine ⟨hh, ?_⟩
        simp only [SimpleGraph.comap_adj]
        simpa [Fin.cast] using hadj
      · rintro ⟨hh, hadj⟩
        refine ⟨hh, ?_⟩
        simp only [SimpleGraph.comap_adj] at hadj
        simpa [Fin.cast] using hadj
    · change (subBlowup Γ V).Adj ⟨w, _⟩ ⟨w', _⟩
          ↔ (subBlowup Γ (fun w => SimpleGraph.comap (Fin.cast (h w)) (V w))).Adj ⟨w, i⟩ ⟨w', i'⟩
      rw [subBlowup_adj_of_fst_ne Γ V hww,
        subBlowup_adj_of_fst_ne Γ (fun w => SimpleGraph.comap (Fin.cast (h w)) (V w)) hww]

/-- Membership transports across a pointwise size-family equality. -/
lemma subBlowup_mem_recast {hc : HeredClass} {n : ℕ} (Γ : SimpleGraph (Fin n)) {s t : Fin n → ℕ}
    (h : ∀ w, s w = t w) (V : ∀ w, SimpleGraph (Fin (t w)))
    (hV : hc.Mem (subBlowup Γ V)) :
    hc.Mem (subBlowup Γ (fun w => SimpleGraph.comap (Fin.cast (h w)) (V w))) :=
  (hc.Mem_congr (subBlowup_recast_iso Γ h V)).mpr hV

/-! ## The blow-up-closure property -/

/-- **Blow-up-closed hereditary class** (`def:blow-up-closed`): for every in-class graph `G`, every
vertex `v`, and every `N`, some order-`N` graph `H` keeps `oneBlowup G v H` in the class.  (The
class *chooses* the interior `H`; this existential is the weakening of substitution-closure that
covers §5–§7 uniformly — see `GraphClass.toBlowupClosed` and the §6/§7 instances.) -/
def BlowupClosed (hc : HeredClass) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V) (N : ℕ),
    hc.Mem G → ∃ (H : SimpleGraph (Fin N)), hc.Mem (oneBlowup G v H)

/-! ## The iteration bridge: single-vertex ⟹ uniform full blow-up -/

/-- **General iteration** (`lem:blowup-iterate`, finset form).  For a prescribed clone-size family
`m` (each class nonempty) and any subset `S` of vertices "already enlarged" — vertices outside `S`
staying singletons — there is a within-class family realising the partial blow-up `S` in the class.
Proved by induction on `S`: the base is the all-singleton blow-up `≃g Γ`; the step enlarges one fresh
singleton clone via `BlowupClosed` and `subBlowupStepIso`. -/
theorem BlowupClosed.subBlowup_partial {hc : HeredClass} (hbc : BlowupClosed hc) {n : ℕ}
    (Γ : SimpleGraph (Fin n)) (hΓ : hc.Mem Γ) (m : Fin n → ℕ) (_hm : ∀ w, 1 ≤ m w)
    (S : Finset (Fin n)) :
    ∃ (W : ∀ w, SimpleGraph (Fin (if w ∈ S then m w else 1))), hc.Mem (subBlowup Γ W) := by
  classical
  induction S using Finset.induction with
  | empty =>
    -- all clone classes are singletons ⟹ `subBlowup Γ W₀ ≃g Γ`
    refine ⟨fun _ => (⊥ : SimpleGraph (Fin (if _ ∈ (∅ : Finset (Fin n)) then m _ else 1))), ?_⟩
    have hsz : ∀ w, (if w ∈ (∅ : Finset (Fin n)) then m w else 1) = 1 := by
      intro w; simp
    exact (hc.Mem_congr (subBlowup_singleton_iso Γ hsz _)).mpr hΓ
  | @insert v S hvS ih =>
    obtain ⟨W', hW'⟩ := ih
    -- The `v`-class of the partial blow-up is a singleton (`v ∉ S`).
    have hav : (if v ∈ S then m v else 1) = 1 := by simp [hvS]
    -- Blow up its unique clone `⟨v, 0⟩` to size `m v` via `BlowupClosed`.
    obtain ⟨H, hH⟩ := hbc (subBlowup Γ W') ⟨v, ⟨0, by rw [hav]; exact Nat.one_pos⟩⟩ (m v) hW'
    -- Transport along the step iso to a genuine sub-blow-up of `Γ`.
    have hmem : hc.Mem (subBlowup Γ (stepFamily v W' H)) :=
      (hc.Mem_congr (subBlowupStepIso Γ v hav W' H)).mp hH
    -- The goal sizes `sz (insert v S)` agree pointwise with the step-family sizes
    -- `update (sz S) v (m v)`.
    have hsize : ∀ w, (if w ∈ insert v S then m w else 1)
        = Function.update (fun w => if w ∈ S then m w else 1) v (m v) w := by
      intro w
      by_cases h : w = v
      · subst h; simp [Function.update_self]
      · simp [h, Finset.mem_insert]
    -- Recast the in-class step blow-up to the goal sizes.
    exact ⟨_, subBlowup_mem_recast Γ hsize (stepFamily v W' H) hmem⟩

/-- **From single vertices to a uniform full blow-up** (`lem:blowup-iterate`).  Blowing up the
vertices of `Γ` one at a time (each to size `M+1`) via `BlowupClosed`, the resulting simultaneous
uniform blow-up `subBlowup Γ W` lies in the class — exactly the hypothesis `subst_root_plantable`
consumes.  The interiors `W` are chosen by the class; the between-class structure is always `Γ`.
Specialises `subBlowup_partial` to `m = fun _ => M+1` and `S = univ`. -/
theorem BlowupClosed.toUniform {hc : HeredClass} (hbc : BlowupClosed hc) {n : ℕ}
    (Γ : SimpleGraph (Fin n)) (hΓ : hc.Mem Γ) (M : ℕ) :
    ∃ (W : ∀ _ : Fin n, SimpleGraph (Fin (M + 1))), hc.Mem (subBlowup Γ W) := by
  classical
  -- Enlarge every vertex to size `M+1`: take the prescribed family `m = fun _ => M+1` and `S = univ`.
  obtain ⟨W, hW⟩ :=
    hbc.subBlowup_partial Γ hΓ (fun _ => M + 1) (fun _ => Nat.le_add_left 1 M) Finset.univ
  -- On `univ` the partial sizes are all `M+1`; recast to the uniform `M+1` family.
  have hsz : ∀ w : Fin n, M + 1 = (if w ∈ (Finset.univ : Finset (Fin n)) then M + 1 else 1) := by
    intro w; simp
  exact ⟨_, subBlowup_mem_recast Γ hsz W hW⟩

/-! ## The unified root-plantability theorem -/

/-- **Blow-up-closed classes are root-plantable** (`thm:blowup-root-plantable`).  The common
generalisation of §5–§7: for any blow-up-closed hereditary class `hc` and non-degenerate type `σ`,
`S_σ = Q_σ`.  Proved by feeding the iteration bridge `toUniform` to `subst_root_plantable`. -/
theorem blowupClosed_root_plantable {hc : HeredClass} (hbc : BlowupClosed hc)
    {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀) :
    RootPlantable (hc.constraintOf σ) :=
  subst_root_plantable hc σ hn₀ (fun Γ hΓ M => hbc.toUniform Γ hΓ M)

/-! ## Clone-closure is a special case (`cor:closures-imply-blowup`(1)) -/

/-- **Clone-closed classes are blow-up-closed** (`cor:closures-imply-blowup`(1)): blow up `v` to an
edgeless graph, which is a one-vertex independent blow-up, in the class by `clone_closed`. -/
theorem GraphClass.toBlowupClosed (gc : GraphClass) : BlowupClosed gc.toHeredClass := by
  intro V _ _ G v N hG
  refine ⟨(⊥ : SimpleGraph (Fin N)), ?_⟩
  -- `oneBlowup G v ⊥ ≃g subBlowup G (oneFamily v ⊥) = independentBlowup G (oneSize v N)`.
  rw [gc.toHeredClass.Mem_congr (oneBlowup_iso G v (⊥ : SimpleGraph (Fin N))),
    subBlowup_oneFamily_bot G v N]
  exact gc.clone_closed G (oneSize v N) hG

/-- **§5 as a corollary of the unified theorem.**  `clone_root_plantable` re-derived through
`blowupClosed_root_plantable` (clone-closed ⟹ blow-up-closed). -/
theorem clone_root_plantable_blowup (gc : GraphClass) {n₀ : ℕ} (σ : FlagType (Fin n₀))
    (hn₀ : 0 < n₀) : RootPlantable (constraintOf gc σ) :=
  blowupClosed_root_plantable gc.toBlowupClosed σ hn₀

end FlagAlgebras.MetaTheory
