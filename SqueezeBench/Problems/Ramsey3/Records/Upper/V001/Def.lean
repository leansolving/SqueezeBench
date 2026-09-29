import SqueezeBench.Problems.Ramsey3.Records.Upper.V000.Def

/-! Record V001 for Ramsey3, upper direction, by baseline claude-opus-5: the record function.

The parity refinement of the Erdős–Szekeres recursion. `R(3,k) ≤ k + R(3,k-1)` becomes
`R(3,k) ≤ k + R(3,k-1) - 1` whenever `k` and the bound on `R(3,k-1)` are both even, because
the extremal colouring would have to be a `(k-1)`-regular graph on an odd number of vertices.
Started at `R(3,2) ≤ 3` the saving applies at every even `k`, and the closed form of the
resulting recursion is `(k² + 3) / 2` in natural division — `k²/2 + 1` for even `k` and
`(k²+3)/2` for odd `k`, against the seed's `k(k+1)/2`.

`minWith` keeps the two values below `nMin`, where `(k²+3)/2` exceeds the seed but `f` is `0`. -/

namespace SqueezeBench.Ramsey3.Upper.V001

/-- The closed form of the parity-refined recursion, valid for `k ≥ nMin`. -/
def v : SqueezeBench.BoundFn := fun k => (k * k + 3) / 2

def record : SqueezeBench.BoundFn := SqueezeBench.minWith SqueezeBench.Ramsey3.Upper.V000.record v

end SqueezeBench.Ramsey3.Upper.V001
