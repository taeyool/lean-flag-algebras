import LeanFlagAlgebras.MetaTheory.TrueClone

/-! # Cluster graphs are root-plantable (paper §6, `cor:cluster-graphs`)

The class of **cluster graphs** — finite disjoint unions of cliques, equivalently the graphs with
no induced `P₃` (path on three vertices) — is hereditary and true-clone-closed (a complete blow-up
of a disjoint union of cliques is again a disjoint union of cliques), so it is root-plantable at
every non-degenerate type by `true_clone_root_plantable`.  It is *not* clone-closed, so this is a
genuinely larger reach than §5.

We encode "no induced `P₃`" as: adjacency is transitive on distinct vertices.  (If `a ∼ b` and
`b ∼ c` with `a ≠ c` then `a ∼ c`; equivalently each connected component is a clique.)
-/

namespace FlagAlgebras.MetaTheory

open SimpleGraph

/-! ## The complete-blow-up adjacency -/

/-- Adjacency in the complete blow-up: two vertices are adjacent iff their base vertices are
`Γ`-adjacent, or they lie in the same clone class and are distinct (the clique edges). -/
lemma completeBlowup_adj_iff {V : Type*} {m : V → ℕ} (Γ : SimpleGraph V)
    (p q : Σ v : V, Fin (m v)) :
    (completeBlowup Γ m).Adj p q ↔ Γ.Adj p.1 q.1 ∨ (p.1 = q.1 ∧ p ≠ q) := by
  obtain ⟨pv, pi⟩ := p
  obtain ⟨qv, qi⟩ := q
  show (Γ.Adj pv qv ∨ ∃ h : qv = pv, (⊤ : SimpleGraph (Fin (m pv))).Adj pi (h ▸ qi))
      ↔ Γ.Adj pv qv ∨ (pv = qv ∧ (⟨pv, pi⟩ : Σ v, Fin (m v)) ≠ ⟨qv, qi⟩)
  refine or_congr_right ?_
  simp only [SimpleGraph.top_adj]
  constructor
  · rintro ⟨h, hne⟩
    cases h
    refine ⟨rfl, ?_⟩
    intro heq
    exact hne (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)
  · rintro ⟨hpv, hne⟩
    subst hpv
    exact ⟨rfl, fun h => hne (by rw [h])⟩

/-! ## The cluster-graph class -/

/-- A graph is a **cluster graph** (a disjoint union of cliques / `P₃`-free) if adjacency is
transitive on distinct vertices. -/
def ClusterMem {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c

/-- The class of cluster graphs as a `HeredClass`: heredity holds because an induced subgraph of a
`P₃`-free graph is `P₃`-free. -/
def clusterClass : HeredClass where
  Mem G := ClusterMem G
  comap f hG := by
    intro a b c hab hbc hac
    have hG' := hG (f a) (f b) (f c) (f.map_adj_iff.mpr hab) (f.map_adj_iff.mpr hbc)
      (fun h => hac (f.injective h))
    exact f.map_adj_iff.mp hG'

/-- **Cluster graphs are true-clone-closed**: a complete blow-up of a cluster graph is a cluster
graph (each clone class is a clique, and the between-class structure inherits transitivity from the
base). -/
theorem clusterClass_trueCloneClosed : TrueCloneClosed clusterClass := by
  intro V _ _ G hG m p q r hpq hqr hpr
  rw [completeBlowup_adj_iff] at hpq hqr ⊢
  rcases hpq with hA | ⟨hB1, hB2⟩ <;> rcases hqr with hC | ⟨hD1, hD2⟩
  · -- both between-class: use transitivity in the base (or same class if projections coincide)
    by_cases hpr1 : p.1 = r.1
    · exact Or.inr ⟨hpr1, hpr⟩
    · exact Or.inl (hG p.1 q.1 r.1 hA hC hpr1)
  · -- p∼q in base, q,r same class: rewrite the second projection
    exact Or.inl (hD1 ▸ hA)
  · -- p,q same class, q∼r in base: rewrite the first projection
    exact Or.inl (hB1 ▸ hC)
  · -- both same class: p.1 = q.1 = r.1, and p ≠ r is given
    exact Or.inr ⟨hB1.trans hD1, hpr⟩

/-- **Cluster graphs are root-plantable** (`cor:cluster-graphs`).  Although the class of cluster
graphs is *not* clone-closed, it is true-clone-closed, so `true_clone_root_plantable` applies at
every non-degenerate type. -/
theorem cluster_root_plantable {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀) :
    RootPlantable (clusterClass.constraintOf σ) :=
  true_clone_root_plantable clusterClass clusterClass_trueCloneClosed σ hn₀

/-- Quotient/ensemble equivalence for cluster graphs. -/
theorem cluster_quotient_iff_ensemble {n₀ : ℕ} (σ : FlagType (Fin n₀)) (hn₀ : 0 < n₀)
    (f : FlagAlgebra σ) :
    QuotientNonneg (clusterClass.constraintOf σ) f ↔ EnsembleNonneg (clusterClass.constraintOf σ) f :=
  true_clone_quotient_iff_ensemble clusterClass clusterClass_trueCloneClosed σ hn₀ f

end FlagAlgebras.MetaTheory
