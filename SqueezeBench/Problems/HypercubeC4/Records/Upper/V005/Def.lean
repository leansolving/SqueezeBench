import SqueezeBench.Problems.HypercubeC4.Records.Upper.V004.Def

/-! Record V005 for HypercubeC4, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Upper/V005.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Upper.V005

-- Two thirds of the edges of the cube: `(2n + 1) · 2ⁿ⁻¹ / 3`.
def v : SqueezeBench.BoundFn := fun n => (2 * n + 1) * 2 ^ (n - 1) / 3

def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.HypercubeC4.Upper.V004.record v

end SqueezeBench.HypercubeC4.Upper.V005
