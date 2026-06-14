import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

/-! # Independent blow-ups (paper §5)

The independent blow-up `G^{\mathbf m}` replaces each vertex `v` of `G` by an independent
clone class of size `m v`, joining the clone classes of `v` and `w` completely whenever
`vw ∈ E(G)` (`def:independent-blow-up`).  We model the vertex set as the sigma type
`Σ v, Fin (m v)` and put `⟨v,i⟩ ∼ ⟨w,j⟩` iff `v ∼ w` in `G` (which is automatically
irreflexive: clones of one vertex are never adjacent).

This file currently contains the construction and its basic combinatorics, including the
fact that blow-ups preserve `K_r`-freeness (the engine behind `cor:clique-free`).  The
quantitative density estimates (`lem:planted-mass`, `lem:planted-estimate`) and the
root-plantability theorem live in later files and build on this construction.
-/

namespace FlagAlgebras.MetaTheory

open SimpleGraph

variable {V : Type*}

/-- The **independent blow-up** `G^{\mathbf m}`: vertex set `Σ v, Fin (m v)`, with two
vertices adjacent iff their base vertices are adjacent in `G`.  Clones of a single vertex
(same base, `G`-non-adjacent to itself) are non-adjacent, i.e. each clone class is an
independent set. -/
def independentBlowup (G : SimpleGraph V) (m : V → ℕ) :
    SimpleGraph (Σ v : V, Fin (m v)) where
  Adj p q := G.Adj p.1 q.1
  symm _ _ h := G.symm h
  loopless p h := G.loopless p.1 h

@[simp]
lemma independentBlowup_adj (G : SimpleGraph V) (m : V → ℕ) (p q : Σ v : V, Fin (m v)) :
    (independentBlowup G m).Adj p q ↔ G.Adj p.1 q.1 := Iff.rfl

/-- The projection `⟨v,i⟩ ↦ v` from the blow-up to `G` is a graph homomorphism. -/
def blowupProj (G : SimpleGraph V) (m : V → ℕ) : independentBlowup G m →g G where
  toFun := Sigma.fst
  map_rel' h := h

/-- On any clique of the blow-up the projection is injective: two adjacent vertices have
adjacent (hence distinct) base vertices, so a clique meets each clone class at most once. -/
lemma blowup_clique_projInjOn (G : SimpleGraph V) (m : V → ℕ)
    {s : Set (Σ v : V, Fin (m v))} (hs : (independentBlowup G m).IsClique s) :
    Set.InjOn Sigma.fst s := by
  intro p hp q hq hpq
  by_contra hne
  have hadj : G.Adj p.1 q.1 := hs hp hq hne
  rw [hpq] at hadj
  exact G.loopless _ hadj

/-- **Blow-ups preserve `K_r`-freeness** (the combinatorial core of `cor:clique-free`): a
clique of the blow-up projects, injectively, to a clique of the same size in `G`. -/
theorem cliqueFree_independentBlowup [DecidableEq V] (G : SimpleGraph V) (m : V → ℕ)
    {r : ℕ} (hG : G.CliqueFree r) : (independentBlowup G m).CliqueFree r := by
  intro s hs
  refine hG (s.image Sigma.fst) ⟨?_, ?_⟩
  · intro a ha b hb hab
    rw [Finset.coe_image, Set.mem_image] at ha hb
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨q, hq, rfl⟩ := hb
    have hpq : p ≠ q := fun h => hab (by rw [h])
    exact hs.isClique hp hq hpq
  · rw [Finset.card_image_of_injOn (blowup_clique_projInjOn G m hs.isClique), hs.card_eq]

/-! ## Good-event projection (`lem:planted-estimate`, the structure-preserving step) -/

/-- **Projection preserves induced structure on a transversal**: on a vertex set `S` meeting
each clone class at most once (so `Sigma.fst` is injective on `S`), the induced subgraph of the
blow-up on `S` is isomorphic, via the projection, to the induced subgraph of `G` on `Sigma.fst ''
S`.  This is the "good event" step of `lem:planted-estimate`: a sampled set with distinct base
vertices induces the same graph as its projection. -/
noncomputable def blowupInduceIso (G : SimpleGraph V) (m : V → ℕ)
    {S : Set (Σ v : V, Fin (m v))} (hinj : Set.InjOn Sigma.fst S) :
    (independentBlowup G m).induce S ≃g G.induce (Sigma.fst '' S) where
  toEquiv := Equiv.Set.imageOfInjOn Sigma.fst S hinj
  map_rel_iff' := by
    intro a b
    rw [SimpleGraph.induce_adj, SimpleGraph.induce_adj, independentBlowup_adj]
    rfl

/-- The **planted labelling** as an induced graph embedding: placing each labelled vertex `i` at
the clone `⟨θ i, c i⟩` embeds the type graph `H` into the blow-up (the type embedding of the
planted flag `(B_N, θ̂)`).  Adjacency is preserved and reflected because the blow-up adjacency of
two clones is the `G`-adjacency of their base vertices. -/
def blowupPlantedEmb {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin k)} (m : Fin n → ℕ)
    (θ : H ↪g G) (c : ∀ i, Fin (m (θ i))) : H ↪g independentBlowup G m where
  toFun i := ⟨θ i, c i⟩
  inj' i j h := θ.injective (congrArg Sigma.fst h)
  map_rel_iff' := by
    intro a b
    rw [independentBlowup_adj]
    exact θ.map_adj_iff

/-! ## Positive probability of the planted root (`lem:planted-mass`) -/

open Finset

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-- All *ordered* induced embeddings of a type graph `H` into the blow-up `G^{\mathbf m}`
(an injective vertex map preserving adjacency and non-adjacency, with the `k` labels in their
prescribed order). -/
noncomputable def blowupEmbeddings (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin k))
    (m : Fin n → ℕ) : Finset (Fin k → Σ v : Fin n, Fin (m v)) :=
  univ.filter fun g =>
    Function.Injective g ∧ ∀ i j, H.Adj i j ↔ (independentBlowup G m).Adj (g i) (g j)

/-- The *planted* embeddings: place each labelled vertex `i` somewhere in the clone class of
`θ i`.  Every choice of clones gives a genuine induced embedding. -/
noncomputable def plantedEmbeddings {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin k)}
    (m : Fin n → ℕ) (θ : H ↪g G) : Finset (Fin k → Σ v : Fin n, Fin (m v)) :=
  univ.image fun (c : ∀ i : Fin k, Fin (m (θ i))) i => (⟨θ i, c i⟩ : Σ v : Fin n, Fin (m v))

/-- There are exactly `∏ᵢ m(θ i)` planted embeddings. -/
lemma plantedEmbeddings_card {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin k)}
    (m : Fin n → ℕ) (θ : H ↪g G) : (plantedEmbeddings m θ).card = ∏ i, m (θ i) := by
  rw [plantedEmbeddings, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_pi]; simp
  · intro c c' hcc
    funext i
    have h := congrFun hcc i
    simpa using h

/-- Planted embeddings really are induced embeddings. -/
lemma plantedEmbeddings_subset {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin k)}
    (m : Fin n → ℕ) (θ : H ↪g G) : plantedEmbeddings m θ ⊆ blowupEmbeddings G H m := by
  intro g hg
  rw [plantedEmbeddings, Finset.mem_image] at hg
  obtain ⟨c, -, rfl⟩ := hg
  rw [blowupEmbeddings, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro a b hab
    exact θ.injective (congrArg Sigma.fst hab)
  · intro i j
    rw [independentBlowup_adj]
    exact θ.map_adj_iff.symm

/-- The total number of induced embeddings is at most `N^k`, `N = ∑ m v`. -/
lemma blowupEmbeddings_card_le (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin k))
    (m : Fin n → ℕ) : (blowupEmbeddings G H m).card ≤ (∑ v, m v) ^ k := by
  calc (blowupEmbeddings G H m).card
      ≤ (univ : Finset (Fin k → Σ v : Fin n, Fin (m v))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = (∑ v, m v) ^ k := by
        rw [Finset.card_univ, Fintype.card_pi]
        simp [Fintype.card_sigma]

/-- **Positive probability of the planted root** (`lem:planted-mass`): when each labelled
clone class is large enough (`m(θ i) ≥ (λ/2k)·N`), a uniformly random induced embedding of
the type into the blow-up is *planted* with probability at least `(λ/2k)^k`. -/
theorem planted_mass {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin k)} (m : Fin n → ℕ)
    (θ : H ↪g G) {lam : ℚ} (hlam : 0 < lam) (hk : 0 < k) (hm : ∀ v, 1 ≤ m v)
    (hsize : ∀ i, lam / (2 * k) * ((∑ v, m v : ℕ) : ℚ) ≤ (m (θ i) : ℚ)) :
    (lam / (2 * k)) ^ k ≤
      ((plantedEmbeddings m θ).card : ℚ) / ((blowupEmbeddings G H m).card : ℚ) := by
  set N : ℕ := ∑ v, m v with hN
  set base : ℚ := lam / (2 * k) with hbase
  have hbase_nonneg : 0 ≤ base := by positivity
  have hPA : (plantedEmbeddings m θ).card ≤ (blowupEmbeddings G H m).card :=
    Finset.card_le_card (plantedEmbeddings_subset m θ)
  have hAN : (blowupEmbeddings G H m).card ≤ N ^ k := blowupEmbeddings_card_le G H m
  have hPpos : 0 < (plantedEmbeddings m θ).card := by
    rw [plantedEmbeddings_card]
    exact Finset.prod_pos fun i _ => lt_of_lt_of_le Nat.zero_lt_one (hm (θ i))
  have hApos : 0 < ((blowupEmbeddings G H m).card : ℚ) := by
    exact_mod_cast lt_of_lt_of_le hPpos hPA
  have hPlow : base ^ k * (N : ℚ) ^ k ≤ ((plantedEmbeddings m θ).card : ℚ) := by
    rw [plantedEmbeddings_card, Nat.cast_prod, ← mul_pow]
    calc (base * (N : ℚ)) ^ k = ∏ _i : Fin k, base * (N : ℚ) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i, ((m (θ i)) : ℚ) := by
          refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => hsize i)
          positivity
  rw [le_div_iff₀ hApos]
  calc base ^ k * ((blowupEmbeddings G H m).card : ℚ)
      ≤ base ^ k * (N : ℚ) ^ k := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hbase_nonneg k)
        exact_mod_cast hAN
    _ ≤ ((plantedEmbeddings m θ).card : ℚ) := hPlow

end FlagAlgebras.MetaTheory
