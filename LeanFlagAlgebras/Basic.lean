import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Finite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic

open Set

def combinations (V : Finset α) (ℓ : ℕ) : Finset (Finset α) :=
  (V.powerset).filter fun V' ↦ V'.card = ℓ

theorem card_comb (V : Finset α) (ℓ : ℕ) : (combinations V ℓ).card = V.card.choose ℓ := by
  sorry

def p (M : SimpleGraph α) (N : SimpleGraph β) [DecidableRel M.Adj] [DecidableRel N.Adj] : ℚ :=
  sorry
