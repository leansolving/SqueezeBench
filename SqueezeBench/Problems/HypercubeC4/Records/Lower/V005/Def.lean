import SqueezeBench.Problems.HypercubeC4.Records.Lower.V004.Def

/-! Record V005 for HypercubeC4, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Lower/V005.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Lower.V005

-- The product construction with a 9-edge `C₄`-free `T ⊆ Q₃` in three fixed directions and
-- V001's parity half in the other `n − 3`: `(2n + 3) · 2ⁿ⁻³` edges for `n ≥ 3`.
def prod3 : SqueezeBench.BoundFn := fun n => if n < 3 then 0 else (2 * n + 3) * 2 ^ (n - 3)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.maxWith SqueezeBench.HypercubeC4.Lower.V004.record prod3

end SqueezeBench.HypercubeC4.Lower.V005
