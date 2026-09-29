import SqueezeBench.Problems.HypercubeC4.Records.Lower.V000.Def

/-! Record V001 for HypercubeC4, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Lower/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Lower.V001

-- Half of the edges of the cube: `n · 2ⁿ⁻¹ / 2`, and `1` at `n = 1`.
def record : SqueezeBench.BoundFn := fun n => n * 2 ^ (n - 2)

end SqueezeBench.HypercubeC4.Lower.V001
