import LeanFlagAlgebras.MetaTheory.C5Free
import LeanFlagAlgebras.MetaTheory.Blowup

/-! # Independent blow-ups of `C₅`-free graphs detect triangles (paper §8)

For comparison with the local root-planting constructions: ordinary independent blow-ups of a
`C₅`-free graph stay `C₅`-free *exactly* when the graph is triangle-free.  This is why a naive
blow-up does not work in general for the `C₅`-free class, motivating the sparse local repair.
-/

open FlagAlgebras SimpleGraph

namespace FlagAlgebras.MetaTheory

attribute [local instance] Classical.propDecidable

/-- Three distinct, pairwise-adjacent vertices form a triangle, contradicting `CliqueFree 3`.
The three `Adj` hypotheses are arranged as the consecutive edges of the triangle `x – y – z – x`
(`is3Clique_triple_iff` packages a `3`-clique as exactly these three adjacencies). -/
private lemma triangle_contra {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hTF : G.CliqueFree 3) {x y z : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z) : False :=
  hTF {x, y, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)

/-- **Blow-ups detect triangles** (`lem:c5-blowup`).  For a `C₅`-free graph `G`, every independent
blow-up of `G` is again `C₅`-free if and only if `G` is triangle-free.  (A `C₅` in a blow-up projects
to a closed `5`-walk in `G`, which contains an odd cycle of length `3` or `5`; conversely a triangle
lifts, in a size-`≥2` blow-up, to a `C₅`.) -/
theorem c5_blowup_free_iff_triangleFree {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : C5g.Free G) :
    (∀ (m : V → ℕ), C5g.Free (independentBlowup G m)) ↔ G.CliqueFree 3 := by
  constructor
  · -- (→) Contrapositive: a triangle `{a,b,c}` lifts to a `C₅` in the size-`2` blow-up, via the
    -- closed `5`-walk `a-b-c-a-b-(a)` lifted to the distinct clones
    -- `⟨a,0⟩,⟨b,0⟩,⟨c,0⟩,⟨a,1⟩,⟨b,1⟩`.
    intro hBlow
    by_contra hTri
    rw [SimpleGraph.CliqueFree] at hTri
    push_neg at hTri
    obtain ⟨s, hs⟩ := hTri
    rw [SimpleGraph.is3Clique_iff] at hs
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := hs
    have hab_ne : a ≠ b := hab.ne
    have hac_ne : a ≠ c := hac.ne
    have hbc_ne : b ≠ c := hbc.ne
    refine hBlow (fun _ => 2) ?_
    apply c5_copy_of_pentagon (independentBlowup G (fun _ => 2))
      (⟨a, 0⟩ : Σ v : V, Fin 2) (⟨b, 0⟩ : Σ v : V, Fin 2) (⟨c, 0⟩ : Σ v : V, Fin 2)
      (⟨a, 1⟩ : Σ v : V, Fin 2) (⟨b, 1⟩ : Σ v : V, Fin 2)
    -- The five cyclic edges become base adjacencies `a~b, b~c, c~a, a~b, b~a` (all triangle edges).
    · show G.Adj a b; exact hab
    · show G.Adj b c; exact hbc
    · show G.Adj c a; exact hac.symm
    · show G.Adj a b; exact hab
    · show G.Adj b a; exact hab.symm
    -- The ten pairwise distinctnesses: distinct base vertex, or same base but distinct `Fin 2` index.
    · exact fun h => hab_ne (congrArg Sigma.fst h)       -- ⟨a,0⟩ ≠ ⟨b,0⟩
    · exact fun h => hac_ne (congrArg Sigma.fst h)       -- ⟨a,0⟩ ≠ ⟨c,0⟩
    · intro h; rw [Sigma.mk.injEq] at h; simp at h        -- ⟨a,0⟩ ≠ ⟨a,1⟩
    · exact fun h => hab_ne (congrArg Sigma.fst h)       -- ⟨a,0⟩ ≠ ⟨b,1⟩
    · exact fun h => hbc_ne (congrArg Sigma.fst h)       -- ⟨b,0⟩ ≠ ⟨c,0⟩
    · exact fun h => hab_ne.symm (congrArg Sigma.fst h)  -- ⟨b,0⟩ ≠ ⟨a,1⟩
    · intro h; rw [Sigma.mk.injEq] at h; simp at h        -- ⟨b,0⟩ ≠ ⟨b,1⟩
    · exact fun h => hac_ne.symm (congrArg Sigma.fst h)  -- ⟨c,0⟩ ≠ ⟨a,1⟩
    · exact fun h => hbc_ne.symm (congrArg Sigma.fst h)  -- ⟨c,0⟩ ≠ ⟨b,1⟩
    · exact fun h => hab_ne (congrArg Sigma.fst h)       -- ⟨a,1⟩ ≠ ⟨b,1⟩
  · -- (←) `G` triangle-free ⟹ every blow-up is `C₅`-free.  A blow-up `C₅`-copy `φ` projects via
    -- `Sigma.fst` to a closed `5`-walk `g 0,…,g 4` in `G` (blow-up adjacency = base adjacency).
    -- Consecutive `g i` are distinct (looplessness); case-bash on the five non-consecutive pairs.
    intro hTF m
    rintro ⟨φ⟩
    set f := φ.toHom with hf_def
    have hf : Function.Injective f := φ.injective'
    set g : Fin 5 → V := fun i => (f i).1 with hg
    have E : ∀ i j : Fin 5, (cycleGraph 5).Adj i j → G.Adj (g i) (g j) := by
      intro i j h
      have := f.map_rel h
      rw [independentBlowup_adj] at this
      exact this
    have e01 : G.Adj (g 0) (g 1) := E 0 1 (by decide)
    have e12 : G.Adj (g 1) (g 2) := E 1 2 (by decide)
    have e23 : G.Adj (g 2) (g 3) := E 2 3 (by decide)
    have e34 : G.Adj (g 3) (g 4) := E 3 4 (by decide)
    have e40 : G.Adj (g 4) (g 0) := E 4 0 (by decide)
    have n01 : g 0 ≠ g 1 := e01.ne
    have n12 : g 1 ≠ g 2 := e12.ne
    have n23 : g 2 ≠ g 3 := e23.ne
    have n34 : g 3 ≠ g 4 := e34.ne
    have n40 : g 4 ≠ g 0 := e40.ne
    -- Each non-consecutive coincidence collapses the closed `5`-walk to a triangle; if none holds,
    -- the five vertices are distinct and form a genuine `C₅` in `G`, contradicting `hG`.
    by_cases c02 : g 0 = g 2
    · exact triangle_contra hTF e23 e34 (c02 ▸ e40.symm)        -- {g2,g3,g4}
    · by_cases c13 : g 1 = g 3
      · exact triangle_contra hTF e34 e40 (c13 ▸ e01).symm      -- {g3,g4,g0}
      · by_cases c24 : g 2 = g 4
        · exact triangle_contra hTF e40 e01 (c24 ▸ e12).symm    -- {g4,g0,g1}
        · by_cases c03 : g 0 = g 3
          · exact triangle_contra hTF e01 e12 (c03 ▸ e23).symm  -- {g0,g1,g2}
          · by_cases c14 : g 1 = g 4
            · exact triangle_contra hTF e12 e23 (c14 ▸ e34).symm -- {g1,g2,g3}
            · exact hG (c5_copy_of_pentagon G (g 0) (g 1) (g 2) (g 3) (g 4)
                e01 e12 e23 e34 e40
                n01 c02 c03 (fun h => n40 h.symm)
                n12 c13 c14 n23 c24 n34)

end FlagAlgebras.MetaTheory
