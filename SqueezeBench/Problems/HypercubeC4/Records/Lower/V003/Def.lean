import SqueezeBench.Problems.HypercubeC4.Records.Lower.V002.Def

/-! Record V003 for HypercubeC4, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Lower/V003.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Lower.V003

-- V002, corrected to the exact values `f 3 = 9` and `f 4 = 24`.
def record : SqueezeBench.BoundFn :=
  SqueezeBench.patch (SqueezeBench.patch SqueezeBench.HypercubeC4.Lower.V002.record 3 9) 4 24

end SqueezeBench.HypercubeC4.Lower.V003
