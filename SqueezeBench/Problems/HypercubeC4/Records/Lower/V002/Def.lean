import SqueezeBench.Problems.HypercubeC4.Records.Lower.V001.Def

/-! Record V002 for HypercubeC4, lower direction, by baseline claude-opus-5: the record function.
Keep the statement of `record` as written; it is copied from
`Challenges/HypercubeC4/Lower/V002.lean`. This file may hold only plain `def` and `abbrev`
(docs/CONTRIBUTING.md). -/

namespace SqueezeBench.HypercubeC4.Lower.V002

-- The parity half of the cube in `n − 1` of the directions, plus every edge of the last one.
def record : SqueezeBench.BoundFn := fun n => if n < 2 then n else (n + 1) * 2 ^ (n - 2)

end SqueezeBench.HypercubeC4.Lower.V002
