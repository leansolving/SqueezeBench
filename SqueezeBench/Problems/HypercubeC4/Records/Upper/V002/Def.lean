import SqueezeBench.Problems.HypercubeC4.Records.Upper.V001.Def

/-! Record V002 for HypercubeC4, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Upper/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Upper.V002

-- Three quarters of the edges of the cube: `¾ · n · 2ⁿ⁻¹`.
def v : SqueezeBench.BoundFn := fun n => 3 * n * 2 ^ (n - 3)

def record : SqueezeBench.BoundFn :=
  SqueezeBench.minWith SqueezeBench.HypercubeC4.Upper.V001.record v

end SqueezeBench.HypercubeC4.Upper.V002
