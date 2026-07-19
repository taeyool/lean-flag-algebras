module

public import LeanFlagAlgebras.Flags.ForbidFreePruned

@[expose] public section

-- Correctness validation (each reduces only the pruned generation, never the full
-- enumeration): the pruned generator produces exactly the known K₃-free class counts
-- (7 of 11 at n=4, 14 of 34 at n=5, 38 of 156 at n=6).
example : (augRepsTriFree 4).length = 7 := by native_decide
example : (augRepsTriFree 5).length = 14 := by native_decide
example : (augRepsTriFree 6).length = 38 := by native_decide

-- The pruned `F`-free representative count matches the count obtained by filtering the full
-- representative list `augReps` — i.e. the generic pruning is sound and complete on these.
example : (augRepsFreeB (qFree K4graph) 4).length
    = ((augReps 4).filter (qFree K4graph 4)).length := by native_decide
example : (augRepsFreeB (qFree K4graph) 5).length
    = ((augReps 5).filter (qFree K4graph 5)).length := by native_decide
example : (augRepsFreeB (qFree C4graph) 4).length
    = ((augReps 4).filter (qFree C4graph 4)).length := by native_decide
example : (augRepsFreeB (qFree C4graph) 5).length
    = ((augReps 5).filter (qFree C4graph 5)).length := by native_decide
example : (augRepsFreeB (qFree C5graph) 5).length
    = ((augReps 5).filter (qFree C5graph 5)).length := by native_decide

-- Family: simultaneously forbidding `K₄` and `C₄` (the multi-graph instance of D3).
example : (augRepsFreeB (qFreeFamily [⟨4, K4graph⟩, ⟨4, C4graph⟩]) 5).length
    = ((augReps 5).filter (qFreeFamily [⟨4, K4graph⟩, ⟨4, C4graph⟩] 5)).length := by native_decide

-- Correctness: the cheap clique generator reproduces the K₃-free class counts (7/14/38), matching
-- `augRepsTriFree` — and reduces by the cheap subset scan, not the generic embedding search.
example : (augRepsFreeB (qCliqueFree 3) 4).length = 7 := by native_decide
example : (augRepsFreeB (qCliqueFree 3) 5).length = 14 := by native_decide
example : (augRepsFreeB (qCliqueFree 3) 6).length = 38 := by native_decide
