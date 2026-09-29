import SqueezeBench.Problems.Ramsey3.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V001.Def

-- `R(3,k) ≥ 3k - 4`: on `Z_{3t+1}` with `t = k-2`, joining the pairs at cyclic distance more
-- than `t` gives a triangle-free graph whose independent sets have at most `t+1 = k-1` vertices.
-- Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Ramsey3.Lower.V002

open SqueezeBench

-- The new bound, padded with `0` below `nMin`.
def v : SqueezeBench.BoundFn := pin nMin (fun k => 3 * k - 4)

-- Folded into the previous record, which is larger at `k = 2, 3, 4, 5`.
def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Ramsey3.Lower.V001.record v

end SqueezeBench.Ramsey3.Lower.V002
