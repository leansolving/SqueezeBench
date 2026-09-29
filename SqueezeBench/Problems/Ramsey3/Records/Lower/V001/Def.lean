import SqueezeBench.Problems.Ramsey3.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V000.Def

-- `R(3,k) ≥ ⌊5(k-1)/2⌋ + 1`: the balanced blow-up of the 5-cycle on `⌊5(k-1)/2⌋` vertices
-- is triangle-free and has independence number at most `k-1`.
-- Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Ramsey3.Lower.V001

open SqueezeBench

-- `5 * (k - 1) / 2 + 1`, in ℕ arithmetic, padded with `0` below `nMin`.
def record : SqueezeBench.BoundFn := pin nMin (fun k => 5 * (k - 1) / 2 + 1)

end SqueezeBench.Ramsey3.Lower.V001
