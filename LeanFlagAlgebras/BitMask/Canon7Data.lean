-- Machine-generated aggregator for the 7-vertex witness data.
import LeanFlagAlgebras.BitMask.Canon7DataW0
import LeanFlagAlgebras.BitMask.Canon7DataW1
import LeanFlagAlgebras.BitMask.Canon7DataW2
import LeanFlagAlgebras.BitMask.Canon7DataW3
import LeanFlagAlgebras.BitMask.Canon7DataW4
import LeanFlagAlgebras.BitMask.Canon7DataW5
import LeanFlagAlgebras.BitMask.Canon7DataW6
import LeanFlagAlgebras.BitMask.Canon7DataW7
import LeanFlagAlgebras.BitMask.Canon7DataPerms
import LeanFlagAlgebras.BitMask.Canon7DataReps

set_option maxRecDepth 100000

namespace FlagAlgebras.Compute.BitMask.Canon7

/-- All 2048 witness chunks, in 64 rows of 32. -/
def wChunks7 : List (List ℕ) :=
  wRows7_0 ++ wRows7_1 ++ wRows7_2 ++ wRows7_3 ++ wRows7_4 ++ wRows7_5 ++ wRows7_6 ++ wRows7_7

end FlagAlgebras.Compute.BitMask.Canon7
