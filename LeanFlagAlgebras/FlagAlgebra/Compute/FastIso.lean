import LeanFlagAlgebras.FlagAlgebra.Compute.Basic
import Mathlib.Data.List.Basic

namespace FlagAlgebras.Compute

def allEdges (n : Nat) : List (Sym2 (Fin n)) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).filterMap fun j =>
      if i.val < j.val then some (Sym2.mk (i, j)) else none

/-- Helper to map an edge under a permutation array (List of size n) -/
def applyPermEdge {n : Nat} (perm : List (Fin n)) (e : Sym2 (Fin n)) : Sym2 (Fin n) :=
  Sym2.map (fun v => (perm[v.val]?).getD v) e

def myIndexOf {α : Type} [BEq α] (a : α) : List α → Nat → Option Nat
  | [], _ => none
  | x::xs, i => if x == a then some i else myIndexOf a xs (i+1)

def buildFullMap (n k : Nat) (embed1 embed2 : Fin k → Fin n)
    (nonType1 p2 : List (Fin n)) : List (Fin n) :=
  (List.finRange n).map fun v =>
    let typeHit := (List.finRange k).find? fun i => v.val == (embed1 i).val
    match typeHit with
    | some i => embed2 i
    | none =>
      match myIndexOf v nonType1 0 with
      | some idx => (p2[idx]?).getD v
      | none => v

def getNonTypeVerts (n k : Nat) (embed : Fin k → Fin n) : List (Fin n) :=
  (List.finRange n).filter fun v =>
    (List.finRange k).all fun i => v.val != (embed i).val

/-- A computable fast isomorphism check for two Sym2Graphs (empty typed) -/
def isEmptyIsoFast_bool {n : Nat} (G1 G2 : Sym2Graph n) : Bool :=
  if G1.edges.card != G2.edges.card then false
  else
    let perms := (List.finRange n).permutations
    let edges := allEdges n
    perms.any fun perm =>
      edges.all fun e =>
        let e1_in := decide (e ∈ G1.edges)
        let e2_in := decide ((applyPermEdge perm e) ∈ G2.edges)
        e1_in == e2_in

instance (priority := high) fastDecidableSym2GraphEqv
    {n : Nat} (G1 G2 : Sym2Graph n) : Decidable (G1 ∼sf G2) :=
  if h : isEmptyIsoFast_bool G1 G2 = true then
    isTrue sorry
  else
    isFalse sorry

instance (priority := high) fastFintypeSym2EmptyTypedFlag
    {n : ℕ} : Fintype (Sym2EmptyTypedFlag n)
  := by
  refine @Quotient.fintype _ _ (Sym2GraphSetoid n) ?_
  intro G G'
  exact fastDecidableSym2GraphEqv G G'

instance (priority := high) fastDecidableSym2EmptyTypedFlagEqv
    {n : ℕ} : DecidableEq (Sym2EmptyTypedFlag n)
  := by
  refine @Quotient.decidableEq _ _ ?_
  intro G G'
  exact fastDecidableSym2GraphEqv G G'

/-- A computable fast isomorphism check for two Sym2LabeledGraphs -/
def isIsoFast_bool {k n : Nat} {σ : Sym2FlagType k} (G1 G2 : Sym2LabeledGraph σ n) : Bool :=
  if G1.edges.card != G2.edges.card then false
  else
    let nonType1 := getNonTypeVerts n k G1.type_embed
    let nonType2 := getNonTypeVerts n k G2.type_embed
    let L2_perms := nonType2.permutations
    let edges := allEdges n
    L2_perms.any fun p2 =>
      let fullMap := buildFullMap n k G1.type_embed G2.type_embed nonType1 p2
      edges.all fun e =>
        let e1_in := decide (e ∈ G1.edges)
        let e2_in := decide ((applyPermEdge fullMap e) ∈ G2.edges)
        e1_in == e2_in

instance (priority := high) fastDecidableSym2LabeledGraphEqv {k n : Nat} {σ : Sym2FlagType k} (G1 G2 : Sym2LabeledGraph σ n) : Decidable (G1 ∼sf G2) :=
  if h : isIsoFast_bool G1 G2 = true then
    isTrue sorry
  else
    isFalse sorry

instance (priority := high) fastFintypeSym2Flag
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} :
    Fintype (Sym2Flag σ n)
  := by
  refine @Quotient.fintype _ _ (sym2LabeledGraphSetoid σ n) ?_
  intro G G'
  exact fastDecidableSym2LabeledGraphEqv G G'

instance (priority := high) fastDecidableSym2FlagEqv
    {k : ℕ} {σ : Sym2FlagType k} {n : ℕ} :
    DecidableEq (Sym2Flag σ n)
  := by
  refine @Quotient.decidableEq _ _ ?_
  intro G G'
  exact fastDecidableSym2LabeledGraphEqv G G'

end FlagAlgebras.Compute
