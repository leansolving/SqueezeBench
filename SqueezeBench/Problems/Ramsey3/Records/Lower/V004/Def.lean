import SqueezeBench.Problems.Ramsey3.Def
import SqueezeBench.Problems.Ramsey3.Records.Lower.V003.Def

-- `R(3,k) ≥ 13⌊(k-1)/4⌋ + 2((k-1) mod 4) + 1`: the *unbalanced* blow-up of the circulant
-- `C₁₃(±1,±5)`. V003 blew every residue class up to the same size `q = ⌊(k-1)/4⌋` and threw the
-- remainder `r = (k-1) mod 4` away. Here the `2r` residues `0, 1, …, 2r-1` get one extra vertex
-- each: an independent set of residues contains no two consecutive ones, so it meets that
-- prefix in at most `r` classes, and the independence number stays `4q + r = k - 1`.
-- Definitions only; validity is proved in `Proof.lean`.

namespace SqueezeBench.Ramsey3.Lower.V004

open SqueezeBench

-- The new bound, padded with `0` below `nMin`.
def v : SqueezeBench.BoundFn := pin nMin (fun k => 13 * ((k - 1) / 4) + 2 * ((k - 1) % 4) + 1)

-- Folded into the previous record, which is larger at the small `k`.
def record : SqueezeBench.BoundFn := maxWith SqueezeBench.Ramsey3.Lower.V003.record v

end SqueezeBench.Ramsey3.Lower.V004
