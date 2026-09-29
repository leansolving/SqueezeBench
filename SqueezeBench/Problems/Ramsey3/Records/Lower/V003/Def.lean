import SqueezeBench.Problems.Ramsey3.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V002.Def

-- `R(3,k) ≥ 13⌊(k-1)/4⌋ + 1`: the balanced blow-up of the circulant `C₁₃(±1,±5)`, the extremal
-- graph for `R(3,5)`. It is triangle-free and its independence number is `4`, so replacing each
-- of the 13 vertices by an independent set of size `q = ⌊(k-1)/4⌋` keeps the graph triangle-free
-- with independence number `4q ≤ k-1` on `13q` vertices. Ratio `13/4`, against `3` for V002.
-- Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Ramsey3.Lower.V003

open SqueezeBench

-- The new bound, padded with `0` below `nMin`.
def v : SqueezeBench.BoundFn := pin nMin (fun k => 13 * ((k - 1) / 4) + 1)

-- Folded into the previous record, which is larger at the small `k` and at `k ≡ 0, 1 (mod 4)`
-- below `k = 32`.
def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Ramsey3.Lower.V002.record v

end SqueezeBench.Ramsey3.Lower.V003
