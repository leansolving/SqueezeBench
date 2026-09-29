import SqueezeBench.Problems.HypercubeC4.Records.Lower.V005.Def

/-! Record V006 for HypercubeC4, lower direction, by trial claude-fable: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Lower/V006.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Lower.V006

-- The Brass–Harborth–Nienborg bound `(n + 2^⌊log₄ n⌋) · 2ⁿ⁻²`, written as `2ⁿ(n + 2^⌊log₄ n⌋) / 4`
-- so that it is `1` at `n = 1` and `0` at `n = 0`; `Nat.log` is fuel-based, cheap for the kernel.
def bhn : SqueezeBench.BoundFn := fun n => 2 ^ n * (n + 2 ^ Nat.log 4 n) / 4

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.HypercubeC4.Lower.V005.record bhn

end SqueezeBench.HypercubeC4.Lower.V006
