import LeanFlagAlgebras.BitMask.Canon7

/-! # BitMask pipeline demo

An interactive tour of the bitmask pipeline — open this file in VS Code
and hover the `#eval` / `#check` lines to see the results in the
infoview. Not part of the build (not imported by the aggregator); edit
freely. -/

namespace FlagAlgebras.Compute.BitMask.Demo

open FlagAlgebras.Compute FlagAlgebras.Compute.BitMask

/-! ## 0. Helpers: build and display masks

A graph on `n` vertices is one natural number; bit `pairIdx n a b`
(for `a < b`) is the edge `{a, b}`. -/

/-- The edge list a mask encodes (readable form of `graphOfMask₂`). -/
def maskEdges (n m : ℕ) : List (ℕ × ℕ) :=
  (finPairs n).filterMap fun p =>
    if m.testBit (pairIdx n p.1.val p.2.val) then some (p.1.val, p.2.val)
    else none

/-- Encode an edge list as a mask. -/
def maskOfEdges (n : ℕ) (es : List (ℕ × ℕ)) : ℕ :=
  es.foldl (fun a e => a ||| (1 <<< pairIdx n (min e.1 e.2) (max e.1 e.2))) 0

/-! ## 1. The representatives

One canonical mask per isomorphism class — 34 / 156 / 1044 classes on
5 / 6 / 7 vertices. -/

#eval Canon5.reps5.length          -- 34
#eval Canon6.reps6.length          -- 156
#eval Canon7.reps7.length          -- 1044

-- The first few 6-vertex representatives, decoded to edge lists
-- (empty graph, one edge, two disjoint edges, path, matching, …):
#eval (Canon6.reps6.take 6).map (maskEdges 6)

/-! ## 2. Canonicalization in action

Two different labelings of the same graph (a path on four of the six
vertices) map to the **same** canonical representative. -/

def pathA : ℕ := maskOfEdges 6 [(0, 1), (1, 2), (2, 3)]
def pathB : ℕ := maskOfEdges 6 [(2, 5), (5, 0), (0, 4)]

#eval maskEdges 6 (Canon6.canonImage pathA)  -- canonical form of pathA
#eval Canon6.canonImage pathA == Canon6.canonImage pathB  -- true

-- And the sweep hands us the *proof* for any mask below `2^15`,
-- with zero extra work:
example : ∃ h ∈ Canon6.reps6, graphOfMask₂ 6 pathA ∼sf graphOfMask₂ 6 h :=
  ⟨_, (Canon6.leaf6_reflect (by decide)).1,
    (Canon6.leaf6_reflect (by decide)).2⟩

/-! ## 3. Forbid-free admissible graphs = a filter over representatives

One sweep serves every forbidden graph. The triangle-free classes: -/

#eval Canon5.k3FreeReps5.length    -- 14
#eval Canon6.k3FreeReps6.length    -- 38
#eval Canon7.k3FreeReps7.length    -- 107

-- The five densest triangle-free 7-vertex classes, as edge lists:
#eval ((Canon7.k3FreeReps7.map (fun h => (maskEdges 7 h)))
  |>.filter (fun es => es.length ≥ 10))

/-! ## 4. The kernel-only theorems the pipeline consumes

`#check` shows the statements; all of them depend only on
`propext, Classical.choice, Quot.sound` — no `native_decide`. -/

-- Completeness: every 7-vertex graph is `∼sf` to a listed decoding.
#check @Canon7.canon7_complete

-- The admissible-flag sets, for ANY forbidden graph `F` — same
-- right-hand side as the pruned generator's completeness lemma:
#check @Canon7.maskFreeFlags7_toFinset_eq

-- Its triangle instance with the literal 107-element list:
#check @Canon7.k3FreeFlags7_toFinset_eq

end FlagAlgebras.Compute.BitMask.Demo
