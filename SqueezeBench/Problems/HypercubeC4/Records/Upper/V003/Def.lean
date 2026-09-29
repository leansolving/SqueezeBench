import SqueezeBench.Problems.HypercubeC4.Records.Upper.V002.Def

/-! Record V003 for HypercubeC4, upper direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Upper/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Upper.V003

def record : SqueezeBench.BoundFn := SqueezeBench.patch SqueezeBench.HypercubeC4.Upper.V002.record 2 3

end SqueezeBench.HypercubeC4.Upper.V003
