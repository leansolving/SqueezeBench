import SqueezeBench.Problems.HypercubeC4.Records.Upper.V000.Def

/-! Record V001 for HypercubeC4, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Upper/V001.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Upper.V001

-- The number of edges of the cube `Qₙ` itself: `n · 2ⁿ⁻¹`.
def record : SqueezeBench.BoundFn := fun n => n * 2 ^ (n - 1)

end SqueezeBench.HypercubeC4.Upper.V001
